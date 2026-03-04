class GaussianSolver {
    constructor(A, b) {
        this.coefficients = A.map((row) => [...row]);
        this.results = [...b];
        this.solution = Array(this.results.length).fill(null);
    }

    async forwardElimination(onStep, shouldCancel) {
        const N = this.coefficients.length;

        for (let i = 0; i < N; i++) {
            if (shouldCancel?.()) {
                throw new Error("run cancelled");
            }

            let pivotRow = i;
            let maxValue = Math.abs(this.coefficients[i][i]);

            for (let j = i; j < N; j++) {
                const candidate = Math.abs(this.coefficients[j][i]);
                if (candidate > maxValue) {
                    maxValue = candidate;
                    pivotRow = j;
                }
            }

            if (maxValue === 0) {
                throw new Error("matrix is singular or nearly singular.");
            }

            if (pivotRow !== i) {
                await onStep?.({ type: "pivot", rows: [i, pivotRow] });
                [this.coefficients[i], this.coefficients[pivotRow]] = [this.coefficients[pivotRow], this.coefficients[i]];
                [this.results[i], this.results[pivotRow]] = [this.results[pivotRow], this.results[i]];
                if (shouldCancel?.()) {
                    throw new Error("run cancelled");
                }
            }

            const divisor = this.coefficients[i][i];
            for (let k = i; k < N; k++) {
                await onStep?.({ type: "divide", row: i, col: k, divisor });
                this.coefficients[i][k] /= divisor;
                if (shouldCancel?.()) {
                    throw new Error("run cancelled");
                }
            }
            await onStep?.({ type: "divide-results", idx: i, divisor });
            this.results[i] /= divisor;
            if (shouldCancel?.()) {
                throw new Error("run cancelled");
            }

            for (let j = i + 1; j < N; j++) {
                const scalar = this.coefficients[j][i];
                if (scalar === 0) {
                    continue;
                }

                for (let k = i; k < N; k++) {
                    await onStep?.({ type: "subtract", rows: [j, i], col: k, scalar });
                    this.coefficients[j][k] -= this.coefficients[i][k] * scalar;
                    if (shouldCancel?.()) {
                        throw new Error("run cancelled");
                    }
                }

                await onStep?.({ type: "subtract-results", idx: j, scalar: scalar });
                this.results[j] -= this.results[i] * scalar;
                if (shouldCancel?.()) {
                    throw new Error("run cancelled");
                }
            }
        }
    }

    async backwardSubstitution(onStep, shouldCancel) {
        const N = this.coefficients.length;

        this.solution[N - 1] = this.results[N - 1];

        for (let i = N - 2; i >= 0; i--) {
            if (shouldCancel?.()) {
                throw new Error("run cancelled");
            }

            let value = 0;
            for (let j = i + 1; j < N; j++) {
                await onStep?.({ type: "dot", row: i, col: j });
                value += this.solution[j] * this.coefficients[i][j];
                if (shouldCancel?.()) {
                    throw new Error("run cancelled");
                }
            }
            this.solution[i] = this.results[i] - value;
            await onStep?.({ type: "back-substitution", idx: i, value: this.solution[i] });
            if (shouldCancel?.()) {
                throw new Error("run cancelled");
            }
        }

        return this.solution;
    }
}

class Visualiser {
    constructor({ matrixContainerId, resultContainerId, solutionContainerId, stepButtonId, resetButtonId, unknownsSliderId, unknownsLabelId, statusId, operationNameId, operationOperandsId, operationExplanationId, precision = 3 }) {
        this.matrixEl = document.getElementById(matrixContainerId);
        this.solutionEl = document.getElementById(solutionContainerId);
        this.resultEl = document.getElementById(resultContainerId);
        this.highlightBox = document.getElementById("highlight-box");
        this.stepButton = document.getElementById(stepButtonId);
        this.resetButton = document.getElementById(resetButtonId);
        this.unknownsSlider = document.getElementById(unknownsSliderId);
        this.unknownsLabel = document.getElementById(unknownsLabelId);
        this.statusEl = document.getElementById(statusId);
        this.operationNameEl = document.getElementById(operationNameId);
        this.operationOperandsEl = document.getElementById(operationOperandsId);
        this.operationExplanationEl = document.getElementById(operationExplanationId);
        this.autoStepButton = document.getElementById("auto-step-button");
        this.speedSlider = document.getElementById("speed-slider");
        this.speedLabel = document.getElementById("speed-label");
        this.precision = precision;

        this.currentMatrix = [];
        this.currentResults = [];
        this.latestStep = null;
        this.pendingStepResolver = null;
        this.isRunning = false;
        this.isAutoStepping = false;
        this.autoStepSpeed = 1;
        this.autoStepInterval = null;
        this.solver = null;
        this.systemSize = this.unknownsSlider ? parseInt(this.unknownsSlider.value, 10) : 10;
        this.hasStartedRun = false;
        this.runId = 0;
        this.cancelRequested = false;
        this.previousSolutionValues = [];

        this.bindControls();
        this.updateHighlightBoxSpeed();
        if (this.speedLabel) {
            this.speedLabel.textContent = `speed: ${this.autoStepSpeed.toFixed(1)}x`;
        }
        this.updateUnknownsLabel();
    }

    bindControls() {
        this.stepButton?.addEventListener("click", () => {
            if (!this.isRunning && this.solver && !this.hasStartedRun) {
                this.hasStartedRun = true;
                this.run().catch((error) => {
                    this.isRunning = false;
                    this.isAutoStepping = false;
                    this.setStepEnabled(true);
                    if (this.autoStepButton) {
                        this.autoStepButton.disabled = true;
                        this.autoStepButton.classList.remove("active");
                        this.autoStepButton.textContent = "autostep";
                    }
                    if (this.speedSlider) {
                        this.speedSlider.disabled = true;
                    }
                    this.setStatus(error.message || "error while solving");
                });
                return;
            }

            if (this.pendingStepResolver && !this.isAutoStepping) {
                this.pendingStepResolver();
                this.pendingStepResolver = null;
            }
        });

        this.resetButton?.addEventListener("click", () => {
            this.cancelCurrentRun();
            this.resetSystem(this.systemSize);
        });

        this.autoStepButton?.addEventListener("click", () => {
            if (this.isRunning) {
                if (this.isAutoStepping) {
                    this.stopAutoStep();
                } else {
                    this.startAutoStep();
                }
            }
        });

        this.speedSlider?.addEventListener("input", (e) => {
            this.autoStepSpeed = parseFloat(e.target.value);
            if (this.speedLabel) {
                this.speedLabel.textContent = `speed: ${this.autoStepSpeed.toFixed(1)}x`;
            }
            this.updateHighlightBoxSpeed();
            if (this.isAutoStepping) {
                this.stopAutoStep();
                this.startAutoStep();
            }
        });

        this.unknownsSlider?.addEventListener("input", (e) => {
            this.systemSize = parseInt(e.target.value, 10);
            this.updateUnknownsLabel();
        });

        this.unknownsSlider?.addEventListener("change", () => {
            this.cancelCurrentRun();
            this.resetSystem(this.systemSize);
        });
    }

    updateUnknownsLabel() {
        if (this.unknownsLabel) {
            this.unknownsLabel.textContent = `unknowns: ${this.systemSize}`;
        }
    }

    resetSystem(N) {
        this.stopAutoStep();
        this.cancelRequested = false;
        this.previousSolutionValues = [];
        this.pendingStepResolver = null;
        this.latestStep = null;
        this.hasStartedRun = false;
        this.solver = null;
        this.setRandomSystem(N);
        this.solver = new GaussianSolver(this.currentMatrix, this.currentResults);
        this.attachSolver(this.solver);
        this.render();

        if (this.operationNameEl) {
            this.operationNameEl.textContent = "waiting to start";
        }
        if (this.operationOperandsEl) {
            this.operationOperandsEl.textContent = "-";
        }
        if (this.operationExplanationEl) {
            this.operationExplanationEl.innerHTML = "click step to begin solving.";
        }

        this.setStatus("ready");
        this.setStepEnabled(true);
        if (this.autoStepButton) {
            this.autoStepButton.disabled = true;
            this.autoStepButton.classList.remove("active");
            this.autoStepButton.textContent = "autostep";
        }
        if (this.speedSlider) {
            this.speedSlider.disabled = true;
        }
    }

    setSystem(A, b) {
        this.currentMatrix = A.map((row) => [...row]);
        this.currentResults = [...b];
        this.render();
    }

    setRandomSystem(N) {
        let solutions = Array(N).fill(0).map(() => Math.floor(Math.random() * 21 - 10));
        let A = Array(N).fill(0).map(() => Array(N).fill(0).map(() => Math.floor(Math.random() * 21 - 10)));
        let b = A.map((row) => row.reduce((sum, val, idx) => sum + val * solutions[idx], 0));
        this.setSystem(A, b);
        this.originalMatrix = A.map((row) => [...row]);
        this.originalResults = [...b];
    }

    attachSolver(solver) {
        this.solver = solver;
        this.syncFromSolver();
    }

    cancelCurrentRun() {
        if (!this.isRunning && !this.pendingStepResolver) {
            return;
        }

        this.cancelRequested = true;
        this.runId += 1;
        this.stopAutoStep();

        if (this.pendingStepResolver) {
            this.pendingStepResolver();
            this.pendingStepResolver = null;
        }

        this.isRunning = false;
    }

    async run() {
        if (!this.solver) {
            return [];
        }

        const activeRunId = ++this.runId;
        this.cancelRequested = false;
        this.isRunning = true;
        this.setStatus("running");
        this.setStepEnabled(true);
        if (this.autoStepButton) {
            this.autoStepButton.disabled = false;
        }
        if (this.speedSlider) {
            this.speedSlider.disabled = false;
        }

        try {
            await this.solver.forwardElimination(
                (step) => this.onStep(step, activeRunId),
                () => this.cancelRequested || activeRunId !== this.runId
            );
            const solution = await this.solver.backwardSubstitution(
                (step) => this.onStep(step, activeRunId),
                () => this.cancelRequested || activeRunId !== this.runId
            );
            this.solution = solution;

            if (this.cancelRequested || activeRunId !== this.runId) {
                return [];
            }

            this.isRunning = false;
            this.isAutoStepping = false;
            this.setStepEnabled(false);
            if (this.resetButton) {
                this.resetButton.disabled = false;
            }
            if (this.unknownsSlider) {
                this.unknownsSlider.disabled = false;
            }
            if (this.autoStepButton) {
                this.autoStepButton.disabled = true;
                this.autoStepButton.classList.remove("active");
                this.autoStepButton.textContent = "autostep";
            }
            if (this.speedSlider) {
                this.speedSlider.disabled = true;
            }
            this.setStatus("solution complete");
            this.render();
            return solution;
        } catch (error) {
            if (this.cancelRequested || activeRunId !== this.runId || error?.message === "run cancelled") {
                return [];
            }
            throw error;
        }
    }

    syncFromSolver() {
        if (!this.solver) {
            return;
        }

        this.currentMatrix = this.solver.coefficients.map((row) => [...row]);
        this.currentResults = [...this.solver.results];
    }

    async onStep(step, activeRunId) {
        if (this.cancelRequested || activeRunId !== this.runId) {
            throw new Error("run cancelled");
        }

        this.latestStep = step;
        this.syncFromSolver();
        this.render();
        this.renderOperationDetails(step);

        if (step.type === "pivot") {
            await this.animatePivotRows(step.rows);
            this.applyLocalPivotSwap(step.rows);
            this.render();
        }

        if (this.isRunning) {
            await this.waitForStepAdvance(activeRunId);
        }
    }

    getMatrixRowCells(rowIdx) {
        if (!this.matrixEl || this.currentMatrix.length === 0) {
            return [];
        }

        const size = this.currentMatrix.length;
        const start = rowIdx * size;
        const end = start + size;
        return Array.from(this.matrixEl.children).slice(start, end);
    }

    getResultRowCell(rowIdx) {
        if (!this.resultEl) {
            return null;
        }
        return this.resultEl.children[rowIdx] || null;
    }

    applyLocalPivotSwap(rows) {
        const [firstRow, secondRow] = rows;
        if (firstRow === secondRow) {
            return;
        }

        [this.currentMatrix[firstRow], this.currentMatrix[secondRow]] = [
            this.currentMatrix[secondRow],
            this.currentMatrix[firstRow]
        ];
        [this.currentResults[firstRow], this.currentResults[secondRow]] = [
            this.currentResults[secondRow],
            this.currentResults[firstRow]
        ];
    }

    async animatePivotRows(rows) {
        const [firstRow, secondRow] = rows;
        if (firstRow === secondRow) {
            return;
        }

        const firstMatrixRow = this.getMatrixRowCells(firstRow);
        const secondMatrixRow = this.getMatrixRowCells(secondRow);
        const firstResultCell = this.getResultRowCell(firstRow);
        const secondResultCell = this.getResultRowCell(secondRow);

        if (firstMatrixRow.length === 0 || secondMatrixRow.length === 0) {
            return;
        }

        const anchorFirst = firstMatrixRow[0];
        const anchorSecond = secondMatrixRow[0];
        const firstRect = anchorFirst.getBoundingClientRect();
        const secondRect = anchorSecond.getBoundingClientRect();
        const deltaY = secondRect.top - firstRect.top;

        const animatedElements = [
            ...firstMatrixRow,
            ...secondMatrixRow,
            firstResultCell,
            secondResultCell
        ].filter(Boolean);

        if (animatedElements.length === 0) {
            return;
        }

        const durationMs = Math.max(90, 320 / this.autoStepSpeed);
        const durationSec = durationMs / 1000;

        if (this.highlightBox) {
            this.highlightBox.style.display = "none";
        }

        animatedElements.forEach((el) => {
            el.style.willChange = "transform";
            el.style.transition = `transform ${durationSec}s ease-in-out`;
        });

        requestAnimationFrame(() => {
            firstMatrixRow.forEach((el) => {
                el.style.transform = `translateY(${deltaY}px)`;
            });
            secondMatrixRow.forEach((el) => {
                el.style.transform = `translateY(${-deltaY}px)`;
            });
            if (firstResultCell) {
                firstResultCell.style.transform = `translateY(${deltaY}px)`;
            }
            if (secondResultCell) {
                secondResultCell.style.transform = `translateY(${-deltaY}px)`;
            }
        });

        await new Promise((resolve) => {
            setTimeout(resolve, durationMs + 30);
        });

        animatedElements.forEach((el) => {
            el.style.transition = "";
            el.style.transform = "";
            el.style.willChange = "";
        });
    }

    waitForStepAdvance(activeRunId) {
        return new Promise((resolve) => {
            if (this.cancelRequested || activeRunId !== this.runId) {
                resolve();
                return;
            }

            if (this.isAutoStepping) {
                const baseDelay = 1000 / this.autoStepSpeed;
                setTimeout(resolve, baseDelay);
            } else {
                this.pendingStepResolver = resolve;
            }
        });
    }

    setStepEnabled(enabled) {
        if (this.stepButton) {
            this.stepButton.disabled = !enabled;
        }
    }

    setStatus(message) {
        if (this.statusEl) {
            this.statusEl.textContent = `status: ${message}`;
        }
    }

    startAutoStep() {
        if (this.isAutoStepping || !this.isRunning) {
            return;
        }
        this.isAutoStepping = true;
        if (this.autoStepButton) {
            this.autoStepButton.classList.add("active");
            this.autoStepButton.textContent = "stop";
        }
        if (this.speedSlider) {
            this.speedSlider.disabled = false;
        }
        this.setStatus("stepping");
        if (this.pendingStepResolver) {
            this.pendingStepResolver();
            this.pendingStepResolver = null;
        }
    }

    stopAutoStep() {
        if (!this.isAutoStepping) {
            return;
        }
        this.isAutoStepping = false;
        if (this.autoStepButton) {
            this.autoStepButton.classList.remove("active");
            this.autoStepButton.textContent = "auto-step";
        }
        if (this.speedSlider) {
            this.speedSlider.disabled = false;
        }
        this.setStatus("paused");
    }

    renderOperationDetails(step) {
        if (!this.operationNameEl || !this.operationOperandsEl || !this.operationExplanationEl || !step) {
            return;
        }

        let operation = "operation";
        let operands = "-";
        let explanation = "";

        if (step.type === "pivot") {
            operation = "pivot";
            operands = `row${step.rows[0]} <-> row${step.rows[1]}`;
            explanation = "swap rows - get large diagonal entry - improves precision/stability";
        } else if (step.type === "divide") {
            operation = "normalise pivot row";
            operands = `A[${step.row},${step.col}] = A[${step.row},${step.col}] / ${this.formatValue(step.divisor)}`;
            explanation = "divide pivot row entries by the pivot so the diagonal becomes 1.";
        } else if (step.type === "divide-results") {
            operation = "normalise right-hand side";
            operands = `b[${step.idx}] = b[${step.idx}] / ${this.formatValue(step.divisor)}`;
            explanation = "apply the same row scaling to the result vector entry.";
        } else if (step.type === "subtract") {
            const [target, pivot] = step.rows;
            operation = "eliminate lower entry";
            operands = `A[${target},${step.col}] = A[${target},${step.col}] - (${this.formatValue(step.scalar)} × A[${pivot},${step.col}])`;
            explanation = "subtract a multiple of the pivot row from a lower row to create seros below the pivot.";
        } else if (step.type === "subtract-results") {
            operation = "update right-hand side";
            operands = `b[${step.idx}] = b[${step.idx}] - (${this.formatValue(step.scalar)} * pivot RHS)`;
            explanation = "apply the same row operation to the result vector.";
        } else if (step.type === "dot") {
            operation = "back substitution dot product";
            operands = `sum += x${step.col} * A[${step.row},${step.col}]`;
            explanation = "accumulate dot product of known solution for back substitution.";
        }

        this.operationNameEl.textContent = operation;
        this.operationOperandsEl.textContent = operands;
        this.operationExplanationEl.textContent = explanation;
    }

    formatValue(value) {
        if (Math.abs(value) < 1e-12) {
            return "0";
        }
        return Number(value.toFixed(this.precision)).toString();
    }

    isHighlightedCell(row, col) {
        if (!this.latestStep) {
            return false;
        }
        return (this.latestStep.type === "subtract" && this.latestStep.rows?.includes(row) && this.latestStep.col === col) ||
                (this.latestStep.type === "divide" && this.latestStep.row === row && this.latestStep.col === col) ||
                (this.latestStep.type === "dot" && this.latestStep.row === row && this.latestStep.col === col);
    }

    isHighlightedResult(idx) {
        if (!this.latestStep) {
            return false;
        }
        return (this.latestStep.type === "subtract-results" && this.latestStep.idx === idx) ||
                (this.latestStep.type === "divide-results" && this.latestStep.idx === idx) ||
                (this.latestStep.type === "pivot" && this.latestStep.rows?.includes(idx));
    }

    updateHighlightBoxSpeed() {
        if (this.highlightBox) {
            const transitionDuration = 0.3 / this.autoStepSpeed;
            this.highlightBox.style.transition = `all ${transitionDuration}s ease`;
        }
    }

    updateHighlightBox() {
        if (!this.highlightBox || !this.latestStep) {
            if (this.highlightBox) {
                this.highlightBox.style.display = "none";
            }
            return;
        }

        let row = -1;
        let col = -1;

        if (this.latestStep.type === "divide" || this.latestStep.type === "dot") {
            row = this.latestStep.row;
            col = this.latestStep.col;
        } else if (this.latestStep.type === "subtract") {
            row = this.latestStep.rows[0];
            col = this.latestStep.col;
        }

        if (row >= 0 && col >= 0) {
            // Get the actual cell element to measure its position
            const size = this.currentMatrix.length;
            const cellIndex = row * size + col;
            const cellEl = this.matrixEl.children[cellIndex];

            if (cellEl) {
                const rect = cellEl.getBoundingClientRect();
                const containerRect = this.matrixEl.parentElement.getBoundingClientRect();

                const left = rect.left - containerRect.left;
                const top = rect.top - containerRect.top;

                this.highlightBox.style.display = "block";
                this.highlightBox.style.left = left + "px";
                this.highlightBox.style.top = top + "px";
            } else {
                this.highlightBox.style.display = "none";
            }
        } else {
            this.highlightBox.style.display = "none";
        }
    }

    onCellClick(event) {
        if (this.isRunning) {
            return;
        }

        const cell = event.target;
        const cellText = cell.textContent;
        
        // Determine if this is a result cell or matrix cell
        let row = -1;
        let col = -1;
        let isResult = false;

        // Check if it's a result cell
        for (let i = 0; i < this.resultEl.children.length; i++) {
            if (this.resultEl.children[i] === cell) {
                row = i;
                isResult = true;
                break;
            }
        }

        // Check if it's a matrix cell
        if (row === -1) {
            const size = this.currentMatrix.length;
            for (let i = 0; i < this.matrixEl.children.length; i++) {
                if (this.matrixEl.children[i] === cell) {
                    row = Math.floor(i / size);
                    col = i % size;
                    break;
                }
            }
        }

        if (row === -1) {
            return;
        }

        const currentValue = isResult ? this.currentResults[row] : this.currentMatrix[row][col];
        
        const input = document.createElement("input");
        input.type = "number";
        input.value = currentValue;
        input.step = "any";
        input.style.width = "100%";
        input.style.height = "100%";
        input.style.border = "2px solid #3b82f6";
        input.style.borderRadius = "6px";
        input.style.background = "#1e293b";
        input.style.color = "#e2e8f0";
        input.style.fontSize = "14px";
        input.style.fontWeight = "500";
        input.style.textAlign = "center";
        input.style.padding = "0";
        input.style.fontFamily = "inherit";
        input.style.boxSizing = "border-box";

        const restore = () => {
            cell.textContent = isResult 
                ? this.formatValue(this.currentResults[row])
                : this.formatValue(this.currentMatrix[row][col]);
        };

        const finalize = () => {
            const newValue = parseFloat(input.value);
            if (!isNaN(newValue)) {
                if (isResult) {
                    this.currentResults[row] = newValue;
                    if (this.solver) {
                        this.solver.results[row] = newValue;
                    }
                } else {
                    this.currentMatrix[row][col] = newValue;
                    if (this.solver) {
                        this.solver.coefficients[row][col] = newValue;
                    }
                }
            }
            restore();
        };

        input.addEventListener("blur", finalize);
        input.addEventListener("keydown", (e) => {
            if (e.key === "Enter") {
                finalize();
            } else if (e.key === "Escape") {
                restore();
            }
        });

        cell.textContent = "";
        cell.appendChild(input);
        input.focus();
        input.select();
    }

    render() {
        if (!this.matrixEl || !this.resultEl || this.currentMatrix.length === 0) {
            return;
        }

        const size = this.currentMatrix.length;
        this.matrixEl.innerHTML = "";
        this.solutionEl.innerHTML = "";
        this.resultEl.innerHTML = "";

        this.matrixEl.style.display = "grid";
        this.matrixEl.style.gridTemplateColumns = `repeat(${size}, 60px)`;
        this.matrixEl.style.gap = "6px";

        this.solutionEl.style.display = "grid";
        this.solutionEl.style.gridTemplateColumns = "60px";
        this.solutionEl.style.gap = "6px";

        this.resultEl.style.display = "grid";
        this.resultEl.style.gridTemplateColumns = "60px";
        this.resultEl.style.gap = "6px";

        for (let row = 0; row < size; row++) {
            for (let col = 0; col < size; col++) {
                const cell = document.createElement("div");
                cell.className = "cell";
                if (this.latestStep?.type === "pivot" && this.latestStep.rows?.includes(row)) {
                    cell.style.outline = "2px solid #f97316";
                    cell.style.outlineOffset = "-2px";
                }
                cell.textContent = this.formatValue(this.currentMatrix[row][col]);
                cell.addEventListener("click", (e) => this.onCellClick(e));
                this.matrixEl.appendChild(cell);
            }

            const solutionCell = document.createElement("div");
            solutionCell.className = "cell";
            solutionCell.style.background = "#334155";
            solutionCell.style.cursor = "default";
            
            let solutionCellText = "";
            let hasSolution = false;
            if (this.solver && this.solver.solution[row] != null) {
                solutionCellText = this.formatValue(this.solver.solution[row]);
                hasSolution = true;
            }
            
            // Check if this is a newly populated solution (for animation)
            const wasPreviouslyEmpty = !this.previousSolutionValues[row];
            const isNewlyPopulated = hasSolution && wasPreviouslyEmpty;
            
            if (isNewlyPopulated) {
                solutionCell.classList.add("solution-cell");
            }
            
            solutionCell.textContent = solutionCellText;
            this.solutionEl.appendChild(solutionCell);
            
            // Update tracking for next render
            if (hasSolution) {
                this.previousSolutionValues[row] = this.solver.solution[row];
            }

            const resultCell = document.createElement("div");
            resultCell.className = "cell";
            if (this.isHighlightedResult(row)) {
                resultCell.classList.add("highlighting");
            }
            if (this.latestStep?.type === "pivot" && this.latestStep.rows?.includes(row)) {
                resultCell.style.outline = "2px solid #f97316";
                resultCell.style.outlineOffset = "-2px";
            }
            resultCell.textContent = this.formatValue(this.currentResults[row]);
            resultCell.addEventListener("click", (e) => this.onCellClick(e));
            this.resultEl.appendChild(resultCell);
        }

        this.updateHighlightBox();
    }


}

(async () => {
    const visualiser = new Visualiser({
        matrixContainerId: "coefficient-matrix",
        solutionContainerId: "solution-vector",
        resultContainerId: "result-vector",
        stepButtonId: "step-button",
        resetButtonId: "reset-button",
        unknownsSliderId: "unknowns-slider",
        unknownsLabelId: "unknowns-label",
        statusId: "status-text",
        operationNameId: "op-name",
        operationOperandsId: "op-operands",
        operationExplanationId: "op-explanation",
        precision: 3
    });
    visualiser.resetSystem(visualiser.systemSize);
})();