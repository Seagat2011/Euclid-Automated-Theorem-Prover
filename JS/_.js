
/*

    TITLE:
    Experimental-Parser.js

    AUTHOR: Seagat2011
    http://eterna.cmu.edu/web/player/90270/
    http://fold.it/port/user/1992490

    VERSION:
    Major.Minor.Release.Build
    0.0.1.0

    DESCRIPTION:
    Experimental Parser

    UPDATED
    Add CallGraph support
    Add Session runtime support (during debug mode)
    Add FastForward support

    TODOS
    Add Multi-thread support via inline Web Workers
    Add async/await and Promise.All support

    STYLEGUIDE:
    http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

    EXAMPLE:
    const ProofStatementA = [
        // Axioms and Lemmas
        "1 + 1 = 2",
        "2 + 2 = 4",
        // Theorem to prove
        "1 + 2 + 1 = 4",
    ];

    SCRIPT TYPE:
    Euclid Tool

*/

let QED;
let guidZ = 1n; // 0n reserved (AXIOM ROOT)
let uuidZ = 1n;
let maskSizeZ = 0n;
let PRIMARYKEY = {};
let LASTPRIME = 3n;
let AxiomsArray = [];
let AxiomsArrayH = {}; // quick lookup
let ProofFoundFlag;
let fastForwardQueue = {};
let rewriteQueue = [];
let sessionRuntimeClockFlag; // debug only
const rewriteOpcodesO = {
    _lhsExpand: 1n,
    _lhsReduce: 2n,
    _rhsExpand: 3n,
    _rhsReduce: 4n,
    _lhsFastForward: 5n,
    _rhsFastForward: 6n,
};
const rewriteOpcodeZtoString = {
    [rewriteOpcodesO._lhsExpand]: "lhs expand",
    [rewriteOpcodesO._lhsReduce]: "lhs reduce",
    [rewriteOpcodesO._rhsExpand]: "rhs expand",
    [rewriteOpcodesO._rhsReduce]: "rhs reduce",
    [rewriteOpcodesO._lhsFastForward]: "lhs fast-forward",
    [rewriteOpcodesO._rhsFastForward]: "rhs fast-forward",
};
let tokenLibraryMap = new Map ();
let tokenLibraryInverseMap = new Map ();
let lhsExpandProofFoundFlag;
let lhsReduceProofFoundFlag;
let rhsExpandProofFoundFlag;
let rhsReduceProofFoundFlag;
let tokenDelimeterRE = new RegExp ("\\s+","g");
let tokenOperatorsRE = new RegExp ("[<~]?=+>?");
let globalTime = 0;
let globalTimeRecord = new Map ();
const newlinesRE = new RegExp ("[\\s\\t]*\\n+[\\t\\s]*","gm");
const lineCommentsRE = new RegExp ("^\/\/");
const codeArea = document.getElementById ('_code_');
const viewArea = document.getElementById ('_view_');
const lineNumbers = document.getElementById ('line-numbers');

class AxiomClass extends Object {
    constructor () {
        super ();

        this.guidZ = null;
        this.lhsZ = 0n;
        this.rhsZ = 0n;
        this.lhsPrimaryKeyZ = 1n;
        this.rhsPrimaryKeyZ = 1n;
        this._callGraph = new Map ();
        this._lhsCallGraph = new Map ();
        this._rhsCallGraph = new Map ();
        this._lhsExpandCallGraph = new Map ();
        this._lhsReduceCallGraph = new Map ();
        this._rhsExpandCallGraph = new Map ();
        this._rhsReduceCallGraph = new Map ();
    }
} // end class AxiomClass

class ProofStepObjectClass extends Object {
    constructor () {
        super ();

        this.guidZ = null;
        this.lhsZ;
        this.rhsZ;
        this.rewriteOpcodeZ = 0n;
        this.lhsPrimaryKeyZ = 1n;
        this.rhsPrimaryKeyZ = 1n;
    }
} // end class ProofStepObjectClass

class CloneableObjectClass {
    constructor (objectToClone = {}) {
      return this.cloneObject (objectToClone);
    }

    cloneObject (obj) {
        const cloneDeep = (value) => {
            if (typeof value !== 'object' || value === null) {
                return value;
            }
            if (typeof value === 'bigint') {
                return BigInt (value.toString ());
            }
            if (Array.isArray (value)) {
                return value.map (cloneDeep);
            }

            const clone = Object.create (Object.getPrototypeOf (value));

            return Object.assign (clone, Object.fromEntries (
                Object.entries (value).map (([key, val]) => [key, cloneDeep (val)])
            ));
        };

        if (Array.isArray (obj)) {
            const clonedArray = obj.map (cloneDeep);

            Object.setPrototypeOf (clonedArray, Object.getPrototypeOf (obj));

            return clonedArray;
        } else {
            Object.setPrototypeOf (this, Object.getPrototypeOf (obj));

            return Object.assign (this, cloneDeep (obj));
        }
    }
} // end class CloneableObjectClass

async function main (proofStatementsA) {

    resetProof ();

    AxiomsArray = initAxiomsArrayF ({ proofStatementsA: proofStatementsA });

    initAxiomCallGraphs ({
        axiomsA: AxiomsArray
        , maskSizeZ: maskSizeZ
        , firstRewriteOnlyFlag: true
        , stackA: []
        , cb: initCallGraphs });

    const theoremA = AxiomsArray.pop ();

    let proofStep = new ProofStepObjectClass ();

    proofStep.guidZ = theoremA.guidZ;
    proofStep.lhsZ = theoremA.lhsZ;
    proofStep.rhsZ = theoremA.rhsZ;
    proofStep.rewriteOpcodeZ = 0n;
    proofStep.lhsPrimaryKeyZ = theoremA.lhsPrimaryKeyZ;
    proofStep.rhsPrimaryKeyZ = theoremA.rhsPrimaryKeyZ;

    rewriteQueue.push ([proofStep]);

    clock ({ valueS: "main" });

    const startTimeZ = performance.now ();

    do {

        // read from (bottom of) rewriteQueue
        proofstackA = rewriteQueue.shift ();

        const proofStepC = lastElementOf ({ valueA: proofstackA });

        rewriteSubnets({ proofStepC: proofStepC, proofstack: proofstackA });
        
        if (ProofFoundFlag)
            break;

        clock ({ valueS: "main" });

    } while (rewriteQueue.length && !ProofFoundFlag);

    const endTimeZ = performance.now ();

    clock ({});

    const totalTimeZ = endTimeZ - startTimeZ;

    let resultArray = [];

    let proofStatusFlag = "";
    let QED_Flag = "";

    if (!ProofFoundFlag && proofstackA.length > 1){
        proofStatusFlag = "Partial-proof found.";
        QED = proofstackA;
    } else if (ProofFoundFlag) {
        proofStatusFlag = "Proof found!";
        QED_Flag = "Q.E.D.";
    }

    if (proofStatusFlag) {
        resultArray.push (proofStatusFlag);
        console.info (proofStatusFlag, /* "\n", QED, */ "\n", QED_Flag);
        
        let _axiom1C = new ProofStepObjectClass ();
        let proofArray = [];
        
        QED.forEach((valueObj, indexZ, thisArray) => {
            if (indexZ > 0) {
                _axiom1C.guidZ = valueObj.guidZ;
                _axiom1C.lhsPrimaryKeyZ = valueObj.lhsPrimaryKeyZ;
                _axiom1C.rhsPrimaryKeyZ = valueObj.rhsPrimaryKeyZ;
                _axiom1C.rewriteOpcodeZ = valueObj.rewriteOpcodeZ;
                const axiom2C = AxiomsArrayH[valueObj.guidZ];
                
                let { phraseString, lhsStringArray, rhsStringArray, rewriteResultZArray, rewriteOpcodeZ } 
                    = processProofStep(_axiom1C, axiom2C, maskSizeZ);
        
                rewriteResultZArray.forEach((valueZ, thatIndexZ, thatArray) => {
                    switch(rewriteOpcodeZ){

                        case 1n:
                        case 2n:
                            // lhs operations
                            _axiom1C.lhsZ = valueZ;
                            rhsStringArray = rhsStringArray.length > 0 
                                ? rhsStringArray 
                                : convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ }) ;
                            const newLhsStringArray = convertBitstream2tokens({ proofStepZ: valueZ, maskSizeZ });
                            proofArray.push(`${newLhsStringArray.join(' ')} = ${rhsStringArray.join(' ')}, ${phraseString[thatIndexZ]}`);                            
                            break;

                        case 3n:
                        case 4n:
                            // rhs operations
                            _axiom1C.rhsZ = valueZ;
                            lhsStringArray = lhsStringArray.length > 0 
                                ? lhsStringArray 
                                : convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ }) ;
                            const newRhsStringArray = convertBitstream2tokens({ proofStepZ: valueZ, maskSizeZ });
                            proofArray.push(`${lhsStringArray.join(' ')} = ${newRhsStringArray.join(' ')}, ${phraseString[thatIndexZ]}`);
                            break;

                    } // end switch(rewriteOpcodeZ)
                }); // end rewriteResultZArray.forEach
                
            } else {
                // Handle the root case
                _axiom1C.guidZ = valueObj.guidZ;
                _axiom1C.lhsZ = valueObj.lhsZ;
                _axiom1C.rhsZ = valueObj.rhsZ;
                _axiom1C.lhsPrimaryKeyZ = valueObj.lhsPrimaryKeyZ;
                _axiom1C.rhsPrimaryKeyZ = valueObj.rhsPrimaryKeyZ;
                _axiom1C.rewriteOpcodeZ = valueObj.rewriteOpcodeZ;

                const lhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ });
                const rhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ });

                proofArray.push(`${lhsStringArray.join(' ')} = ${rhsStringArray.join(' ')}, (root)`);
            } // end if (indexZ > 0)
        }); // end QED.forEach

        resultArray.push (proofArray.join ('\n'), QED_Flag);
        
        function processProofStep (_axiom1C, _axiom2C, maskSizeZ) {

            const _guidZ = _axiom1C.guidZ;
            let rewriteOpcodeZ = _axiom1C.rewriteOpcodeZ;
            let phraseString = [];

            let lhsStringArray = [];
            let rhsStringArray = [];
            let rewriteResultZArray = [];
        
            switch (rewriteOpcodeZ) {
                case 1n: // lhsExpand
                    phraseString.push (`(${rewriteOpcodeZtoString[rewriteOpcodeZ]}) via axiom_${_guidZ}`);
                    rhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ });
                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                        proofStepZ: _axiom1C.lhsZ, 
                        maskSizeZ, 
                        fromZ: _axiom2C.rhsZ,
                        toZ: _axiom2C.lhsZ 
                    });
                    break;
                case 2n: // lhsReduce
                    phraseString.push (`(${rewriteOpcodeZtoString[rewriteOpcodeZ]}) via axiom_${_guidZ}`);
                    rhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.rhsZ, maskSizeZ });
                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                        proofStepZ: _axiom1C.lhsZ, 
                        maskSizeZ, 
                        fromZ: _axiom2C.lhsZ,
                        toZ: _axiom2C.rhsZ 
                    });
                    break;
                case 3n: // rhsExpand
                    phraseString.push (`(${rewriteOpcodeZtoString[rewriteOpcodeZ]}) via axiom_${_guidZ}`);
                    lhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ });
                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                        proofStepZ: _axiom1C.rhsZ, 
                        maskSizeZ, 
                        fromZ: _axiom2C.rhsZ,
                        toZ: _axiom2C.lhsZ 
                    });
                    break;
                case 4n: // rhsReduce
                    phraseString.push (`(${rewriteOpcodeZtoString[rewriteOpcodeZ]}) via axiom_${_guidZ}`);
                    lhsStringArray = convertBitstream2tokens({ proofStepZ: _axiom1C.lhsZ, maskSizeZ });
                    rewriteResultZArray = replaceBitfieldsInProofStepBigEndian({ 
                        proofStepZ: _axiom1C.rhsZ, 
                        maskSizeZ, 
                        fromZ: _axiom2C.lhsZ,
                        toZ: _axiom2C.rhsZ 
                    });
                    break;
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

                case 6n: // rhs f/f
                    const rhsReduceFastForwardKey = `lhs:${_axiom1C.rhsPrimaryKeyZ}`;

                    const rhsFasftForwardResultAway = fastForwardQueue[rhsReduceFastForwardKey];

                    rhsFasftForwardResultAway.forEach((_valueZ, tooIndexZ, tooArray) => {
                        if (tooIndexZ > 0) {
                            rewriteOpcodeZ = _valueZ.rewriteOpcodeZ;
                            _axiom1C.guidZ = _valueZ.guidZ;
                            _axiom1C.rewriteOpcodeZ = _valueZ.rewriteOpcodeZ;
                            phraseString.push( `(${rewriteOpcodeZtoString[rewriteOpcodeZ]}) via axiom_${_valueZ.guidZ} (using fast-forward rhs)`);
                            const __axiom2C = AxiomsArrayH[_valueZ.guidZ];

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
                            
                        } else {
                            switch(_valueZ.rewriteOpcodeZ){
                                case 1n:
                                case 2n:
                                // overwite rhs
                                _axiom1C.rhsZ = _valueZ.rhsZ;
                                break;

                                case 3n:
                                case 4n:
                                // overwrite lhs
                                _axiom1C.lhsZ = _valueZ.lhsZ;
                            }
                        } // end if (tooIndexZ)
                    });

                    break;

            }
        
            return { phraseString, lhsStringArray, rhsStringArray, rewriteResultZArray, rewriteOpcodeZ };
        };

    } else {
        resultArray.push ('No proof found.');
        console.info ("No proof found.");
    }

    console.info (`Total runtime: ${totalTimeZ} Milliseconds`);
    resultArray.push (`Total runtime: ${totalTimeZ} Milliseconds`);

    codeArea.value = resultArray.join('\n\n');

} // end main

function resetProof () {
    QED = null;
    guidZ = uuidZ; // 0n reserved (AXIOM ROOT)
    maskSizeZ = 0n;
    AxiomsArray = [];
    AxiomsArrayH = {}; // quick lookup
    LASTPRIME = 3n;
    rewriteQueue = [];
    fastForwardQueue = {};
    ProofFoundFlag = false;
    tokenLibraryMap = new Map ();
    tokenLibraryInverseMap = new Map ();
    sessionRuntimeClockFlag = false; // debug only
    lhsExpandProofFoundFlag = false;
    lhsReduceProofFoundFlag = false;
    rhsExpandProofFoundFlag = false;
    rhsReduceProofFoundFlag = false;
} // end resetProof

function initAxiomsArrayF ({ proofStatementsA = [] }) {

    clock ({ valueS: "initAxiomsArrayF" });

    // First pass: build token library and calculate maskSizeZ
    let _proofStatementsA = [];

    proofStatementsA
        .split(newlinesRE)
            .forEach (statement => {
                if (/^[\w\{]/.test(statement)){
                    const retArray = statement
                        .split (tokenDelimeterRE);

                    retArray
                        .forEach (token => {
                            if (!tokenLibraryMap.has (token)) {
                                const local_uuid = nextPrime ();
                                tokenLibraryMap.set (token, local_uuid);
                                tokenLibraryInverseMap.set (local_uuid, token);
                            }
                        });

                    _proofStatementsA.push (retArray);
                }
            }); // end proofStatementsA.split

    maskSizeZ = resolutionOf({ valueZ: LASTPRIME });

    // Second pass: create and populate axiom objects
    let _guidZ = 1n;
    let axiomObjArray = [];
    let visitedMap = new Map ();

    _proofStatementsA
        .forEach ((statement, indexZ, thisArrayA) => {
            let i = 0n;
            let contentsZArray = [0n];
            let primaryKeyZArray = [1n];

            statement
                .forEach (token => {
                    if (token.match (tokenOperatorsRE)) {
                        ++i;
                    } else {
                        if (i >= contentsZArray.length) {
                            contentsZArray.push (0n);
                            primaryKeyZArray.push (1n);
                        }
                        const tokenValue = tokenLibraryMap.get (token);
                        contentsZArray[i] = (contentsZArray[i] << maskSizeZ) | tokenValue;
                        primaryKeyZArray[i] *= tokenValue;
                    }
                });

            let _guid2PartZ = 0n;

            contentsZArray
                .forEach((_, i, array) => {
                    for (let j = i + 1; j < array.length; j++) {
                        const lhsZ = array[i] >= array[j] ? array[i] : array[j];
                        const rhsZ = array[i] >= array[j] ? array[j] : array[i];
                        const lhsPkeyZ = array[i] >= array[j] ? primaryKeyZArray[i] : primaryKeyZArray[j] ;
                        const rhsPkeyZ = array[i] >= array[j] ? primaryKeyZArray[j] : primaryKeyZArray[i] ;
                        const visitedString = `${lhsZ}:${rhsZ}`;

                        if (!visitedMap.has (visitedString)) {
                            visitedMap.set (visitedString, true);
                            const axiomObj = new AxiomClass();
                            axiomObj.guidZ = indexZ < thisArrayA.length - 1 ? `${_guidZ}.${_guid2PartZ++}` : 0n;
                    
                            // Ensure lhs > rhs for proper expand/reduce operation
                            axiomObj.lhsZ = lhsZ;
                            axiomObj.rhsZ = rhsZ;
                            axiomObj.lhsPrimaryKeyZ = lhsPkeyZ;
                            axiomObj.rhsPrimaryKeyZ = rhsPkeyZ;
                    
                            // Catalog for quick-lookup
                            AxiomsArrayH[axiomObj.guidZ] = axiomObj;
                    
                            axiomObjArray.push(axiomObj);
                        }
                    }
                });

            _guidZ++;

        }); // end _proofStatementsA.forEach 

    clock ({ valueS: 'initAxiomsArrayF' })

    return axiomObjArray;

} // end initAxiomsArrayF

function processAxioms ({
    axiomsA
    , maskSizeZ
    , firstRewriteOnlyFlag = false
    , stackA = []
    , cb = null
}) {

    clock ({ valueS: "processAxioms" });

    axiomsA.forEach (axioms1C => {
        AxiomsArray
        .map (axioms2C =>
            compareAxioms ({
                axioms1C: axioms1C,
                axioms2C: axioms2C,
                maskSizeZ: maskSizeZ,
                firstRewriteOnlyFlag: firstRewriteOnlyFlag
            })
        )
        .forEach (result => cb ({
            axioms1C: axioms1C,
            resultObj: result,  // contains { axioms2C, _resultObj }
            stackA: stackA
        }))
    });

    clock ({ valueS: 'processAxioms' });

} // end processAxioms

function compareAxioms ({
    axioms1C
    , axioms2C
    , maskSizeZ
    , firstRewriteOnlyFlag = false
}) {

    if (axioms1C.guidZ === axioms2C.guidZ)
        return {};

    clock ({ valueS: "compareAxioms" });

    let _resultObj = {
        _lhsExpand: false
        , _lhsReduce: false
        , _rhsExpand: false
        , _rhsReduce: false
    };

    if (!firstRewriteOnlyFlag){

        const lhsExpandFastForward = `lhs:${axioms1C.guidZ}:expand:${axioms2C.guidZ}`;
        const lhsReduceFastForward = `lhs:${axioms1C.guidZ}:reduce:${axioms2C.guidZ}`;
        const rhsExpandFastForward = `rhs:${axioms1C.guidZ}:expand:${axioms2C.guidZ}`;
        const rhsReduceFastForward = `rhs:${axioms1C.guidZ}:reduce:${axioms2C.guidZ}`;
        
        if (fastForwardQueue[lhsExpandFastForward] /* && axioms1C.lhsPrimaryKeyZ%axioms2C.rhsPrimaryKeyZ === 0n */){
            _resultObj._lhsExpand = [axioms1C.lhsPrimaryKeyZ/axioms2C.rhsPrimaryKeyZ*axioms2C.lhsPrimaryKeyZ];
        }
        if (fastForwardQueue[lhsReduceFastForward] /* && axioms1C.lhsPrimaryKeyZ%axioms2C.lhsPrimaryKeyZ === 0n */){
            _resultObj._lhsReduce = [axioms1C.lhsPrimaryKeyZ/axioms2C.lhsPrimaryKeyZ*axioms2C.rhsPrimaryKeyZ];
        }    
        if (fastForwardQueue[rhsExpandFastForward] /* && axioms1C.rhsPrimaryKeyZ%axioms2C.rhsPrimaryKeyZ === 0n */){
            _resultObj._rhsExpand = [axioms1C.rhsPrimaryKeyZ/axioms2C.rhsPrimaryKeyZ*axioms2C.lhsPrimaryKeyZ];
        }
        if (fastForwardQueue[rhsReduceFastForward] /* && axioms1C.rhsPrimaryKeyZ%axioms2C.lhsPrimaryKeyZ === 0n */){
            _resultObj._rhsReduce = [axioms1C.rhsPrimaryKeyZ/axioms2C.lhsPrimaryKeyZ*axioms2C.rhsPrimaryKeyZ];
        }

     } else if (axioms2C.guidZ != 0n){
        
        _resultObj._lhsExpand = axioms1C.lhsPrimaryKeyZ%axioms2C.rhsPrimaryKeyZ === 0n;
        _resultObj._lhsReduce = axioms1C.lhsPrimaryKeyZ%axioms2C.lhsPrimaryKeyZ === 0n;
        _resultObj._rhsExpand = axioms1C.rhsPrimaryKeyZ%axioms2C.rhsPrimaryKeyZ === 0n;
        _resultObj._rhsReduce = axioms1C.rhsPrimaryKeyZ%axioms2C.lhsPrimaryKeyZ === 0n;

     }

    clock ({ valueS: "compareAxioms" });

    return { axioms2C, _resultObj };

} // end compareAxioms

function rewriteSubnets ({
    proofStepC
    , proofstack
}) {

    const axiom1C = AxiomsArrayH[proofStepC.guidZ];

    clock ({ valueS: "rewriteSubnets" });

    rewriteSubnet_lhsExpand({ _proofStepC: proofStepC, _proofstack: proofstack, _subnetH: axiom1C._lhsExpandCallGraph });
    rewriteSubnet_lhsReduce({ _proofStepC: proofStepC, _proofstack: proofstack, _subnetH: axiom1C._lhsReduceCallGraph });
    rewriteSubnet_rhsExpand({ _proofStepC: proofStepC, _proofstack: proofstack, _subnetH: axiom1C._rhsExpandCallGraph });
    rewriteSubnet_rhsReduce({ _proofStepC: proofStepC, _proofstack: proofstack, _subnetH: axiom1C._rhsReduceCallGraph });

    function rewriteSubnet_lhsExpand ({ _proofStepC, _proofstack, _subnetH }) {
        if (ProofFoundFlag)
            return;

        for (let [indexZ, _] of _subnetH) {
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

    function rewriteSubnet_lhsReduce ({ _proofStepC, _proofstack, _subnetH }) {
        if (ProofFoundFlag)
            return;

        for (let [indexZ, _] of _subnetH) {
            const _axiom2C = AxiomsArrayH[indexZ];
            if (_proofStepC.lhsPrimaryKeyZ % _axiom2C.lhsPrimaryKeyZ === 0n) {
                const newProofStepC = new CloneableObjectClass (_proofStepC);
                newProofStepC.guidZ = _axiom2C.guidZ;
                newProofStepC.rewriteOpcodeZ = rewriteOpcodesO._lhsReduce;
                newProofStepC.lhsPrimaryKeyZ = newProofStepC.lhsPrimaryKeyZ / _axiom2C.lhsPrimaryKeyZ * _axiom2C.rhsPrimaryKeyZ;
                const newProofStack = [..._proofstack, newProofStepC];
                rewriteQueue.push([..._proofstack, newProofStepC]);
                updateProofFoundFlag ({ _proofStepC: newProofStepC, _proofstack: newProofStack});
            }
        }
    }

    function rewriteSubnet_rhsExpand ({ _proofStepC, _proofstack, _subnetH }) {
        if (ProofFoundFlag)
            return;

        for (let [indexZ, _] of _subnetH) {
            const _axiom2C = AxiomsArrayH[indexZ];
            if (_proofStepC.rhsPrimaryKeyZ % _axiom2C.rhsPrimaryKeyZ === 0n) {
                const newProofStepC = new CloneableObjectClass (_proofStepC);
                newProofStepC.guidZ = _axiom2C.guidZ;
                newProofStepC.rewriteOpcodeZ = rewriteOpcodesO._rhsExpand;
                newProofStepC.rhsPrimaryKeyZ = newProofStepC.rhsPrimaryKeyZ / _axiom2C.rhsPrimaryKeyZ * _axiom2C.lhsPrimaryKeyZ;
                const newProofStack = [..._proofstack, newProofStepC];
                rewriteQueue.push([..._proofstack, newProofStepC]);
                updateProofFoundFlag ({ _proofStepC: newProofStepC, _proofstack: newProofStack});
            }
        }
    }

    function rewriteSubnet_rhsReduce ({ _proofStepC, _proofstack, _subnetH }) {
        if (ProofFoundFlag)
            return;

        for (let [indexZ, _] of _subnetH) {
            const _axiom2C = AxiomsArrayH[indexZ];
            if (_proofStepC.rhsPrimaryKeyZ % _axiom2C.lhsPrimaryKeyZ === 0n) {
                const newProofStepC = new CloneableObjectClass (_proofStepC);
                newProofStepC.guidZ = _axiom2C.guidZ;
                newProofStepC.rewriteOpcodeZ = rewriteOpcodesO._rhsReduce;
                newProofStepC.rhsPrimaryKeyZ = newProofStepC.rhsPrimaryKeyZ / _axiom2C.lhsPrimaryKeyZ * _axiom2C.rhsPrimaryKeyZ;
                const newProofStack = [..._proofstack, newProofStepC];
                rewriteQueue.push([..._proofstack, newProofStepC]);
                updateProofFoundFlag ({ _proofStepC: newProofStepC, _proofstack: newProofStack});
            }
        }
    }

    function updateProofFoundFlag({ _proofStepC, _proofstack }) {
        if (ProofFoundFlag)
            return;

        ProofFoundFlag = (_proofStepC.lhsPrimaryKeyZ == _proofStepC.rhsPrimaryKeyZ);

        if (ProofFoundFlag)
            QED = _proofstack;

    }

} // end rewriteSubnets

function rewriteProofstepF ({
    axioms1C    
    , resultObj: { axioms2C, _resultObj } = {}
    , stackA
}) {

    if (_resultObj == null) 
        return false;

    if (axioms1C.lhsPrimaryKeyZ == axioms1C.rhsPrimaryKeyZ) {
        QED = stackA;
        ProofFoundFlag = true;
        return true;
    }

    const result = checkProofStep(axioms1C, proofstackA);

    if (result.ProofFoundFlag) {
        QED = result.QED;
        ProofFoundFlag = true;
        return true;
    }

    const resultsA = [
        { values: _resultObj._lhsExpand }
        , { values: _resultObj._lhsReduce }
        , { values: _resultObj._rhsExpand }
        , { values: _resultObj._rhsReduce }
    ].map (({ values }, indexZ, thisArrayA) => {
        if (!values?.length) return false;

        let currentProofChain = [...stackA];

        for (let valueZ of values) {
            let proofStep = new ProofStepObjectClass ();

            proofStep.guidZ = axioms2C.guidZ;

            switch (indexZ) {
                case 0:
                proofStep.lhsPrimaryKeyZ = valueZ;
                proofStep.rhsPrimaryKeyZ = axioms1C.rhsPrimaryKeyZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._lhsExpand;
                break;

                case 1:
                proofStep.lhsPrimaryKeyZ = valueZ;
                proofStep.rhsPrimaryKeyZ = axioms1C.rhsPrimaryKeyZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._lhsReduce;
                break;

                case 2:
                proofStep.lhsPrimaryKeyZ = axioms1C.lhsPrimaryKeyZ;
                proofStep.rhsPrimaryKeyZ = valueZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._rhsExpand;
                break;

                case 3:
                proofStep.lhsPrimaryKeyZ = axioms1C.lhsPrimaryKeyZ;
                proofStep.rhsPrimaryKeyZ = valueZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._rhsReduce;
                break;
            }

            const proofFound = (proofStep.lhsPrimaryKeyZ === proofStep.rhsPrimaryKeyZ);

            currentProofChain.push (proofStep);

            rewriteQueue.push (currentProofChain);

            if (proofFound) {
                QED = [...currentProofChain];
                ProofFoundFlag = true;
                return QED;
            }
        }

        return false;
    });

    [ lhsExpandProofFoundFlag, lhsReduceProofFoundFlag, rhsExpandProofFoundFlag, rhsReduceProofFoundFlag ] = resultsA;

} // end rewriteProofstepF

function checkProofStep(proofStepC, proofstackA) {
    const lhsFastKey = createFastKey('lhs', proofStepC.lhsPrimaryKeyZ);
    const rhsFastKey = createFastKey('rhs', proofStepC.rhsPrimaryKeyZ);

    updateFastForwardQueue(lhsFastKey);
    updateFastForwardQueue(rhsFastKey);

    const lhsFastKeySearch = createFastKey('rhs', proofStepC.lhsPrimaryKeyZ);
    const rhsFastKeySearch = createFastKey('lhs', proofStepC.rhsPrimaryKeyZ);

    const lhsResult = queryFastForwardQueue('lhs', lhsFastKeySearch, proofStepC.lhsPrimaryKeyZ, null);
    if (lhsResult) 
        return lhsResult;

    const rhsResult = queryFastForwardQueue('rhs', rhsFastKeySearch, null, proofStepC.rhsPrimaryKeyZ);
    if (rhsResult) 
        return rhsResult;

    return { QED: null, ProofFoundFlag: false };

    // Local function declarations

    function createFastKey(prefix, value) {
        return `${prefix}:${value}`;
    }

    function updateFastForwardQueue(key) {
        if (!fastForwardQueue[key]) {
            fastForwardQueue[key] = [...proofstackA];
        }
    }

    function createProofStep(indirS, lhs, rhs, valueObj) {
        const proofStep = new ProofStepObjectClass();
        const lhsFlag = /^lhs/.test(indirS);
        proofStep.guidZ = valueObj.guidZ;
        proofStep.lhsPrimaryKeyZ = lhsFlag ? lhs : valueObj.lhsPrimaryKeyZ;
        proofStep.rhsPrimaryKeyZ = lhsFlag ? valueObj.rhsPrimaryKeyZ : rhs;
        proofStep.rewriteOpcodeZ = lhsFlag ? rewriteOpcodesO._lhsFastForward : rewriteOpcodesO._rhsFastForward;
        return proofStep;
    }

    function queryFastForwardQueue(indirS, searchKey, lhs, rhs) {
        if (fastForwardQueue[searchKey]) {
            const _QED = [...proofstackA];
            fastForwardQueue[searchKey].forEach((value, indexZ, thisArray) => {
                _QED.push(createProofStep(indirS, lhs, rhs, value));
            });
            return { QED: _QED, ProofFoundFlag: true };
        }
        return null;
    }

} // end checkProofStep

function clock ({ valueS }) {
    if (!sessionRuntimeClockFlag) return;

    if (valueS) {
        const localTime = performance.now () - globalTime;
        let currentValue = globalTimeRecord.get (valueS) || 0;
        currentValue += localTime;
        globalTimeRecord.set (valueS, currentValue);
        globalTime = localTime;
    } else {
        for (const [key, val] of globalTimeRecord) {
            console.info (`Total runtime (${key}): ${val} Milliseconds`);
        }
    }
} // end clock

function initCallGraphs ({
    axioms1C
    , resultObj
    , stackA 
}) {

    if (isNotEmpty ({ targ:resultObj })) {
        const { axioms2C, _resultObj } = resultObj;

        const retArray = [
            _resultObj._lhsExpand
            , _resultObj._lhsReduce
            , _resultObj._rhsExpand
            , _resultObj._rhsReduce
        ]
        .forEach ((valueA, indexZ, thisArrayA) => {
            if (valueA == false)
                return;
            
            switch (indexZ) {
                case 0: axioms1C._lhsExpandCallGraph.set (axioms2C.guidZ, true); break;
                case 1: axioms1C._lhsReduceCallGraph.set (axioms2C.guidZ, true); break;
                case 2: axioms1C._rhsExpandCallGraph.set (axioms2C.guidZ, true); break;
                case 3: axioms1C._rhsReduceCallGraph.set (axioms2C.guidZ, true); break;
            }
            
        });
    }
} // end initCallGraphs

function convertBitstream2tokens ({ proofStepZ, maskSizeZ }) {    

    clock ({ valueS: "bitstream2tokens" });

    let ret = [];
    const chunkMask = (1n << maskSizeZ) - 1n;
    const proofStepResolutionZ = resolutionOf ({ valueZ: proofStepZ });

    let bitsRemainingZ = proofStepResolutionZ;

    // ensure read/write masks are properly aligned
    while (bitsRemainingZ > maskSizeZ) {

        if (bitsRemainingZ > maskSizeZ)
            bitsRemainingZ -= maskSizeZ;

    }

    // ensure all offsets align to (Resolution % maskSizeZ) boundaries
    const proofstepOffsetZ = proofStepResolutionZ - bitsRemainingZ;

    for (let ii = proofstepOffsetZ; ii >= 0n; ii -= maskSizeZ) {
        const chunk = (proofStepZ >> ii) & chunkMask;
        tokenLibraryInverseMap.has (chunk) && ret.push (tokenLibraryInverseMap.get (chunk));
    } // end loop

    return ret;

} // end convertBitstream2tokens

function replaceBitfieldsInProofStepBigEndian ({
    proofStepZ
    , maskSizeZ
    , fromZ
    , toZ
    , firstRewriteOnlyFlag = false 
}) {    

    clock ({ valueS: "replaceBitfieldsInProofStepBigEndian" });

    const fromResolutionZ = resolutionOf ({ valueZ: fromZ });
    const proofStepResolutionZ = resolutionOf ({ valueZ: proofStepZ });

    const subnetNotFoundFlag = (fromResolutionZ > proofStepResolutionZ);

    let ret = [];

    if (subnetNotFoundFlag)
        return ret;

    const _fastForwardKey = `${proofStepZ}:${fromZ}:${toZ}`;

    if (fastForwardQueue[_fastForwardKey]) {
        ret = fastForwardQueue[_fastForwardKey];

        return ret;
    }

    let resultZ = 0n;
    let fullRewriteFoundFlag = false;
    const chunkMask = (1n << maskSizeZ) - 1n;
    const toResolutionZ = resolutionOf ({ valueZ: toZ });
    
    const nonMatchSubnetLengthsFlag = (fromResolutionZ !== proofStepResolutionZ);

    let bitsRemainingZ = proofStepResolutionZ;
    let fromOffsetBitsRemainingZ = fromResolutionZ;
    let toOffsetBitsRemainingZ = toResolutionZ;

    // ensure read/write masks are properly aligned
    while (bitsRemainingZ > maskSizeZ
        || fromOffsetBitsRemainingZ > maskSizeZ
        || toOffsetBitsRemainingZ > maskSizeZ) {

        if (bitsRemainingZ > maskSizeZ)
            bitsRemainingZ -= maskSizeZ;

        if (fromOffsetBitsRemainingZ > maskSizeZ)
            fromOffsetBitsRemainingZ -= maskSizeZ;

        if (toOffsetBitsRemainingZ > maskSizeZ)
            toOffsetBitsRemainingZ -= maskSizeZ;
    }

    let lastPushedValue = null;

    // ensure all offsets align to (Resolution % maskSizeZ) boundaries
    const proofstepOffsetZ = proofStepResolutionZ - bitsRemainingZ;
    let fromOffsetZ = fromResolutionZ - fromOffsetBitsRemainingZ;
    const fromOffsetResetZ = fromResolutionZ - fromOffsetBitsRemainingZ;
    const toOffsetZ = toResolutionZ + (maskSizeZ - toOffsetBitsRemainingZ);

    for (let ii = proofstepOffsetZ; ii >= 0n; ii -= maskSizeZ) {
        const chunk = (proofStepZ >> ii) & chunkMask;
        const chunkFrom = (fromZ >> fromOffsetZ) & chunkMask;

        if (chunk === chunkFrom) {
            if (fromOffsetZ > 0n) {
                fromOffsetZ -= maskSizeZ;
            } else {
                fromOffsetZ = fromOffsetResetZ;
                resultZ = (resultZ << toOffsetZ) | toZ;
                const intermediateOffsetZ = ii;

                const intermediateMaskZ = (1n << intermediateOffsetZ) - 1n;

                const intermediateRewriteZ = (resultZ << intermediateOffsetZ) | (proofStepZ & intermediateMaskZ);

                if (lastPushedValue !== intermediateRewriteZ) {
                    ret.push (intermediateRewriteZ);
                    lastPushedValue = intermediateRewriteZ;
                }

                if (!fullRewriteFoundFlag) {
                    if (firstRewriteOnlyFlag)
                        return ret;

                    fullRewriteFoundFlag = true;
                }

            }
        } else if (nonMatchSubnetLengthsFlag) {
            resultZ = (resultZ << maskSizeZ) | chunk;
        } else {
            return [];
        }
    } // end loop

    clock ({ valueS: 'replaceBitfieldsInProofStepBigEndian'});

    fastForwardQueue[_fastForwardKey] = [...ret];

    // No full rewrites found
    if (!fullRewriteFoundFlag)
        return [];

    return ret;
} // end replaceBitfieldsInProofStepBigEndian

function resolutionOf ({ valueZ }) {
    const I = BigInt (valueZ.toString (2).length);

    return I;
} // end resolutionOf

function updateLineNumbers () {
    const lines = viewArea.value.split ('\n');
    lineNumbers.innerHTML = lines.map ((_, index) => index + 1).join ('<br>');
} // end updateLineNumbers

function lastElementOf ({ valueA }) {
    let ret;
    const ii = valueA.length - 1;

    if (valueA[ii]) {
        ret = valueA[ii];
    }

    return ret;
} // end lastElementOf

function isNotEmpty ({ targ }) {
    const resultFlag = Object.keys (targ).length > 0;

    return resultFlag;
} // end isNotEmpty

function isEmpty ({ targ }) {
    const resultFlag = isNotEmpty ({ targ: targ });

    return !resultFlag;
} // end isNotEmpty

function initAxiomCallGraphs ({
    axiomsA
    , maskSizeZ
    , firstRewriteOnlyFlag = true
    , stackA = []
    , cb = null
}) {

    clock ({ valueS: "initAxiomCallGraphs" });

    const I = AxiomsArray.length;
    const II = AxiomsArray.length * 2 - 1;

    // 2-pass as acting src and targ
    for (let i = 0; i < II; ++i){
        const ii = (i < I ? i : I - i%I - 2) ;
        processAxioms ({
            axiomsA: [AxiomsArray[ii]]
            , maskSizeZ: maskSizeZ
            , firstRewriteOnlyFlag: true
            , stackA: stackA
            , cb: cb });
    }  

    clock ({ valueS: 'initAxiomCallGraphs'});

} // end initAxiomCallGraphs

function isPrime (num) {
    if (num <= 1n) return false;
    if (num <= 3n) return true;

    // Check divisibility from 2 to the square root of num
    for (let i = 2n; i * i <= num; ++i) {
      if (num % i === 0n) return false;
    }
    return true;
} // end isPrime

function nextPrime () {
    var num = LASTPRIME;
    while (true) {
      if (isPrime(num)) {
        LASTPRIME = num + 2n;
        return num;
      }
      num += 2n; // only check odd numbers //
    }
} // end nextPrime

try {

    viewArea.addEventListener ('keyup', function () {
        updateLineNumbers ();
        try {
            codeArea.value = "Working...";
            main (this.value);
        } catch (e) {
            e.stack = e.stack
                .split (/\n/g)
                    .filter (s => s)
                        .map ((s,idx,me) => `${me.length-idx-1}: ${s}`)
                            .join ("\n");
            const errorDetails = {
                  name: e.name,
                  message: e.message,
                  lineNumber: e.lineNumber,
                  columnNumber: e.columnNumber,
              };
            codeArea.value = JSON.stringify (errorDetails, null, 2) + `\n\ncall stack:\n${e.stack}`;
        }
    });

    viewArea.addEventListener ('scroll', function () {
        lineNumbers.scrollTop = this.scrollTop;
    });

    viewArea.value = viewArea.value.length > 0 
        ? viewArea.value 
        : '// Axioms and Lemmas\n1 + 1 = 2\n2 + 2 = 4\n// Theorem to prove\n1 + 2 + 1 = 4';

    codeArea.value = '';

    updateLineNumbers ();

} catch (e) {

    e.stack = e.stack
        .split (/\n/g)
            .filter (s => s)
                .map ((s,idx,me) => `${me.length-idx-1}: ${s}`)
                    .join ("\n");

    const errorDetails = {
            name: e.name,
            message: e.message,
            lineNumber: e.lineNumber,
            columnNumber: e.columnNumber,
        };

    _code_.value = JSON.stringify (errorDetails, null, 2) + `\n\ncall stack:\n${e.stack}`;
}