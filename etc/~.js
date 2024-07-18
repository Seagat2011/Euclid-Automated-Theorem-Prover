
const lhsExpandFlag = AxiomsArrayH[axioms1C.guidZ]._lhsExpandCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;
const lhsReduceFlag = AxiomsArrayH[axioms1C.guidZ]._lhsReduceCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;
const rhsExpandFlag = AxiomsArrayH[axioms1C.guidZ]._rhsExpandCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;
const rhsReduceFlag = AxiomsArrayH[axioms1C.guidZ]._rhsReduceCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;

const NUM_WORKERS = 4; // Number of workers in the pool
const TOTAL_ITERATIONS = 100; // Total number of iterations

// Worker code as a string
const workerCode = `
  self.onmessage = function(e) {
    const { iteration, previousValue } = e.data;
    // Simulating some computation that depends on the previous value
    const result = previousValue * 2 + iteration;
    self.postMessage({ iteration, result });
  };
`;

// Create a pool of workers
const workerPool = [];
for (let i = 0; i < NUM_WORKERS; i++) {
  const blob = new Blob([workerCode], { type: 'application/javascript' });
  const workerUrl = URL.createObjectURL(blob);
  workerPool.push(new Worker(workerUrl));
}

// Function to process iterations
async function processIterations() {
  let previousValue = 1; // Initial value
  
  for (let i = 0; i < TOTAL_ITERATIONS; i++) {
    const worker = workerPool[i % NUM_WORKERS];
    
    const result = await new Promise((resolve) => {
      worker.onmessage = (e) => resolve(e.data.result);
      worker.postMessage({ iteration: i, previousValue });
    });
    
    console.log(`Iteration ${i}: ${result}`);
    previousValue = result; // Update previousValue for the next iteration
  }
  
  // Clean up workers
  workerPool.forEach(worker => worker.terminate());
}

processIterations().then(() => console.log('All iterations completed'));