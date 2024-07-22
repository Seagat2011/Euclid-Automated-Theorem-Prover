

function rewriteSubnet_lhsExpand ({ _proofStepC, _proofstack, _subnetH }) {
    if (ProofFoundFlag)
        return;

    let _subnetsArray = [];

    _proofStepC.lhsExpandCallGraphMap.length > 1 
        && _proofStepC
            .lhsExpandCallGraphMap
                .forEach((valueZ, indexZ,thisArray) => {
                    _subnetsArray.push(indexZ);
                });

    _subnetH
        .forEach((valueZ, indexZ,thisArray) => {
        _subnetsArray.push(indexZ);
    });

    for (let indexZ of _subnetH) {
        const _axiom2C = AxiomsArrayH[indexZ];
        if (_proofStepC.lhsPrimaryKeyZ % _axiom2C.rhsPrimaryKeyZ === 0n) {
            const newProofStepC = new CloneableObjectClass (_proofStepC);
            newProofStepC.guidZ = _axiom2C.guidZ;
            newProofStepC.rewriteOpcodeZ = rewriteOpcodesO._lhsExpand;
            newProofStepC.lhsPrimaryKeyZ = newProofStepC.lhsPrimaryKeyZ / _axiom2C.rhsPrimaryKeyZ * _axiom2C.lhsPrimaryKeyZ;
            const newProofStack = [..._proofstack, newProofStepC];
            rewriteQueue.push(newProofStack);
            updateProofFoundFlag ({ _proofStepC: newProofStepC, _proofstack: newProofStack});
        }
    }
}

case 5n: // lhs f/f
const lhsReduceFastForwardKey = `rhs:${_axiom1C.lhsPrimaryKeyZ}`;

const lhsFasftForwardResultAway = fastForwardQueue[lhsReduceFastForwardKey];

lhsFasftForwardResultAway.forEach((_valueZ, tooIndexZ, tooArray) => {
    if (tooIndexZ > 0) {
        rewriteOpcodeZ = _valueZ.rewriteOpcodeZ;
        _axiom1C.guidZ = _valueZ.guidZ;
        _axiom1C.rewriteOpcodeZ = _valueZ.rewriteOpcodeZ;
        const __axiom2C = AxiomsArrayH[_valueZ.guidZ];
        phraseString.push( `(${rewriteOpcodeZtoString[rewriteOpcodeZ]}) via axiom_${_valueZ.guidZ} (using fast-forward lhs)`);
        
        processProofStep(_axiom1C, __axiom2C, maskSizeZ);
        /* 
        switch(rewriteOpcodeZ) {
            case 1n:
                // lhs expand
                lhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ });
                rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                    proofStepZ: _axiom1C.lhsZ, 
                    maskSizeZ, 
                    fromZ: __axiom2C.rhsZ,
                    toZ: __axiom2C.lhsZ 
                });
                break;

            case 2n:
                // lhs reduce
                lhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ });
                rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                    proofStepZ: _axiom1C.lhsZ, 
                    maskSizeZ, 
                    fromZ: __axiom2C.lhsZ,
                    toZ: __axiom2C.rhsZ 
                });
                break;

            case 3n: 
                // rhs expand
                rhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ });
                rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                    proofStepZ: _axiom1C.rhsZ, 
                    maskSizeZ, 
                    fromZ: __axiom2C.rhsZ,
                    toZ: __axiom2C.lhsZ 
                });
                break;

            case 4n:
                // rhs reduce
                rhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ });
                rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                    proofStepZ: _axiom1C.rhsZ, 
                    maskSizeZ, 
                    fromZ: __axiom2C.lhsZ,
                    toZ: __axiom2C.rhsZ 
                });
                break;

        } // end switch(rewriteOpcodeZ)
         */
    } else {
        switch(_valueZ.rewriteOpcodeZ){
            case 1n:
            case 2n:
            // overwite lhs
            _axiom1C.lhsZ = _valueZ.lhsZ;
            break;

            case 3n:
            case 4n:
            // overwrite rhs
            _axiom1C.rhsZ = _valueZ.rhsZ;
        }
    } // end if (tooIndexZ)
});

break;

                            /* 
                            switch(rewriteOpcodeZ) {
                                case 1n:
                                    // lhs expand
                                    lhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ });
                                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                                        proofStepZ: _axiom1C.lhsZ, 
                                        maskSizeZ, 
                                        fromZ: __axiom2C.rhsZ,
                                        toZ: __axiom2C.lhsZ 
                                    });
                                    break;

                                case 2n:
                                    // lhs reduce
                                    lhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ });
                                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                                        proofStepZ: _axiom1C.lhsZ, 
                                        maskSizeZ, 
                                        fromZ: __axiom2C.lhsZ,
                                        toZ: __axiom2C.rhsZ 
                                    });
                                    break;

                                case 3n: 
                                    // rhs expand
                                    rhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ });
                                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                                        proofStepZ: _axiom1C.rhsZ, 
                                        maskSizeZ, 
                                        fromZ: __axiom2C.rhsZ,
                                        toZ: __axiom2C.lhsZ 
                                    });
                                    break;

                                case 4n:
                                    // rhs reduce
                                    rhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ });
                                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                                        proofStepZ: _axiom1C.rhsZ, 
                                        maskSizeZ, 
                                        fromZ: __axiom2C.lhsZ,
                                        toZ: __axiom2C.rhsZ 
                                    });
                                    break;

                            } // end switch(rewriteOpcodeZ)
                             */

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