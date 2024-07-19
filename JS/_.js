
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
        this._callGraph = {};
        this._lhsCallGraph = {};
        this._rhsCallGraph = {};
        this._lhsExpandCallGraph = {};
        this._lhsReduceCallGraph = {};
        this._rhsExpandCallGraph = {};
        this._rhsReduceCallGraph = {};
    }
} // end class AxiomClass

class ProofStepObjectClass extends Object {
    constructor () {
        super ();

        this.guidZ = null;
        this.rewriteOpcodeZ = 0n;
        this.lhsZ;
        this.rhsZ;
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
/* 
    let proofStepObj = new ProofStepObjectClass ();
    proofStepObj.guidZ = axioms1C.guidZ;
    proofStepObj.lhsZ = axioms1C.lhsZ;
    proofStepObj.rhsZ = axioms1C.rhsZ;
    proofStepObj.rewriteOpcodeZ = 0n;
    fastForwardQueue[`lhs:${axioms1C.lhsZ}`] = [proofStepObj];
    fastForwardQueue[`rhs:${axioms1C.rhsZ}`] = [proofStepObj];
     */

    if (isNotEmpty ({ targ:resultObj })) {
        const { axioms2C, _resultObj } = resultObj;

        const retArray = [
            _resultObj._lhsExpand
            , _resultObj._lhsReduce
            , _resultObj._rhsExpand
            , _resultObj._rhsReduce
        ]
        .forEach ((valueA, indexZ, thisArrayA) => {
            if (valueA?.length < 1)
                return;

            switch (indexZ) {
                case 0: axioms1C._lhsExpandCallGraph[axioms2C.guidZ] = true; axioms1C._lhsCallGraph[axioms2C.guidZ] = true; break;
                case 1: axioms1C._lhsReduceCallGraph[axioms2C.guidZ] = true; axioms1C._lhsCallGraph[axioms2C.guidZ] = true; break;
                case 2: axioms1C._rhsExpandCallGraph[axioms2C.guidZ] = true; axioms1C._rhsCallGraph[axioms2C.guidZ] = true; break;
                case 3: axioms1C._rhsReduceCallGraph[axioms2C.guidZ] = true; axioms1C._rhsCallGraph[axioms2C.guidZ] = true; break;
            }
        });
    }
} // end initCallGraphs

function rewriteProofstepF ({
    axioms1C    
    , resultObj: { axioms2C, _resultObj } = {}
    , stackA
}) {
    if (_resultObj == null) return;

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
                proofStep.lhsZ = valueZ;
                proofStep.rhsZ = axioms1C.rhsZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._lhsExpand;
                break;

                case 1:
                proofStep.lhsZ = valueZ;
                proofStep.rhsZ = axioms1C.rhsZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._lhsReduce;
                break;

                case 2:
                proofStep.lhsZ = axioms1C.lhsZ;
                proofStep.rhsZ = valueZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._rhsExpand;
                break;

                case 3:
                proofStep.lhsZ = axioms1C.lhsZ;
                proofStep.rhsZ = valueZ;
                proofStep.rewriteOpcodeZ = rewriteOpcodesO._rhsReduce;
                break;
            }

            const proofFound = (proofStep.lhsZ === proofStep.rhsZ);

            currentProofChain.push (proofStep);

            rewriteQueue.push (currentProofChain);

            if (proofFound) return [...currentProofChain];
        }

        return false;
    });

    [ lhsExpandProofFoundFlag, lhsReduceProofFoundFlag, rhsExpandProofFoundFlag, rhsReduceProofFoundFlag ] = resultsA;

} // end rewriteProofstepF

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

    //const lhsCallGraphFlag = AxiomsArrayH[axioms1C.guidZ]._lhsCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;
    //const rhsCallGraphFlag = AxiomsArrayH[axioms1C.guidZ]._rhsCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;

    //if (lhsCallGraphFlag) {
        _resultObj._lhsExpand = replaceBitfieldsInProofStepBigEndian ({
            proofStepZ: axioms1C.lhsZ
            , maskSizeZ: maskSizeZ
            , fromZ: axioms2C.rhsZ
            , toZ: axioms2C.lhsZ
            , firstRewriteOnlyFlag: firstRewriteOnlyFlag });

        _resultObj._lhsReduce = replaceBitfieldsInProofStepBigEndian ({
            proofStepZ: axioms1C.lhsZ
            , maskSizeZ: maskSizeZ
            , fromZ: axioms2C.lhsZ
            , toZ: axioms2C.rhsZ
            , firstRewriteOnlyFlag: firstRewriteOnlyFlag });
    //}

    //if (rhsCallGraphFlag) {
        _resultObj._rhsExpand = replaceBitfieldsInProofStepBigEndian ({
            proofStepZ: axioms1C.rhsZ
            , maskSizeZ: maskSizeZ
            , fromZ: axioms2C.rhsZ
            , toZ: axioms2C.lhsZ
            , firstRewriteOnlyFlag: firstRewriteOnlyFlag });

        _resultObj._rhsReduce = replaceBitfieldsInProofStepBigEndian ({
            proofStepZ: axioms1C.rhsZ
            , maskSizeZ: maskSizeZ
            , fromZ: axioms2C.lhsZ
            , toZ: axioms2C.rhsZ
            , firstRewriteOnlyFlag: firstRewriteOnlyFlag });
    //}

    clock ({ valueS: "compareAxioms" });

    return { axioms2C, _resultObj };

} // end compareAxioms

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
                                tokenLibraryMap.set (token, guidZ);
                                tokenLibraryInverseMap.set (guidZ, token);
                                guidZ++;
                            }
                        });

                    _proofStatementsA.push (retArray);
                }
            }); // end proofStatementsA.split

    maskSizeZ = resolutionOf({ valueZ: guidZ });

    // Second pass: create and populate axiom objects
    let axiomObjArray =[];

    _proofStatementsA
        .forEach ((statement, indexZ, thisArrayA) => {
            let i = 0n;
            let contentsZArray = [0n];

            statement
                .forEach (token => {
                    if (token.match (tokenOperatorsRE)) {
                        ++i;
                    } else {
                        if (i >= contentsZArray.length) {
                            contentsZArray.push (0n);
                        }
                        const tokenValue = tokenLibraryMap.get (token);
                        contentsZArray[i] = (contentsZArray[i] << maskSizeZ) | tokenValue;
                    }
                });

            contentsZArray
                .forEach ((_, j, thatArray) => {
                    if (j > 0n) {
                        i = 0n;
                        do {
                            const axiomObj = new AxiomClass ();
                            axiomObj.guidZ = indexZ < thisArrayA.length - 1 ? BigInt (indexZ + 1) : 0n;

                            // Ensure lhs > rhs for proper expand/reduce operation
                            axiomObj.lhsZ = thatArray[i] >= thatArray[j] ? thatArray[i] : thatArray[j] ;
                            axiomObj.rhsZ = thatArray[i] >= thatArray[j] ? thatArray[j] : thatArray[i] ;

                            // Catalog for quick-lookup
                            AxiomsArrayH[axiomObj.guidZ] = axiomObj;

                            axiomObjArray.push (axiomObj);

                        } while (++i < j);
                    }
                });
        }); // end _proofStatementsA.forEach 

    clock ({ valueS: 'initAxiomsArrayF' })

    return axiomObjArray;

} // end initAxiomsArrayF

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

function resetProof () {
    QED = null;
    guidZ = uuidZ; // 0n reserved (AXIOM ROOT)
    maskSizeZ = 0n;
    AxiomsArray = [];
    AxiomsArrayH = {}; // quick lookup
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

function checkProofStep(proofStepC, proofstackA) {
    const lhsFastKey = createFastKey('lhs', proofStepC.lhsZ);
    const rhsFastKey = createFastKey('rhs', proofStepC.rhsZ);

    updateFastForwardQueue(lhsFastKey);
    updateFastForwardQueue(rhsFastKey);

    const lhsFastKeySearch = createFastKey('rhs', proofStepC.lhsZ);
    const rhsFastKeySearch = createFastKey('lhs', proofStepC.rhsZ);

    const lhsResult = queryFastForwardQueue('lhs', lhsFastKeySearch, proofStepC.lhsZ, null);
    if (lhsResult) 
        return lhsResult;

    const rhsResult = queryFastForwardQueue('rhs', rhsFastKeySearch, null, proofStepC.rhsZ);
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
        proofStep.lhsZ = lhsFlag ? lhs : valueObj.lhsZ;
        proofStep.rhsZ = lhsFlag ? valueObj.rhsZ : rhs;
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

async function main (proofStatementsA) {

    resetProof ();

    AxiomsArray = initAxiomsArrayF ({ proofStatementsA: proofStatementsA });
/* 
    initAxiomCallGraphs ({
        axiomsA: AxiomsArray
        , maskSizeZ: maskSizeZ
        , firstRewriteOnlyFlag: true
        , stackA: []
        , cb: initCallGraphs }); */

    const theoremA = AxiomsArray.pop (); // lastElementOf({ valueA: AxiomsArray }); // Theorem is the last element!

    let proofStep = new ProofStepObjectClass ();

    proofStep.guidZ = theoremA.guidZ;
    proofStep.lhsZ = theoremA.lhsZ;
    proofStep.rhsZ = theoremA.rhsZ;
    proofStep.rewriteOpcodeZ = 0n;

    rewriteQueue.push ([proofStep]);

    clock ({ valueS: "main" });

    const startTimeZ = performance.now ();

    do {

        // read from (bottom of) rewriteQueue
        proofstackA = rewriteQueue.shift ();

        const proofStepC = lastElementOf ({ valueA: proofstackA });

        const result = checkProofStep(proofStepC, proofstackA);

        if (result.ProofFoundFlag) {
            // Use result.QED
            QED = result.QED;
            break;
        }

        // clone rewrite candidates for each subnet
        const _pfc = new CloneableObjectClass (proofStepC);

        processAxioms ({
            axiomsA: [_pfc]
            , maskSizeZ: maskSizeZ
            , firstRewriteOnlyFlag: false
            , stackA: proofstackA
            , cb: rewriteProofstepF });

        if (!ProofFoundFlag){
            QED = lhsExpandProofFoundFlag
            || lhsReduceProofFoundFlag
            || rhsExpandProofFoundFlag
            || rhsReduceProofFoundFlag;

            ProofFoundFlag = QED && (QED.length > 0);
        }

        if (ProofFoundFlag)
            break;

        clock ({ valueS: "main" });

    } while (rewriteQueue.length && !ProofFoundFlag);

    const endTimeZ = performance.now ();

    clock ({});

    const totalTimeZ = endTimeZ - startTimeZ;

    let resultArray = []

    if (QED) {
        resultArray.push ('Proof found!');
        console.info ("Proof found!", "\n", QED, "\n", "Q.E.D.");

        let proofArray = [];
        QED.forEach ((valueObj, indexZ, thisArrayA) => {
            const phraseString =  
                `(${ indexZ > 0 ? rewriteOpcodeZtoString[valueObj.rewriteOpcodeZ] : "root"}) via ${ valueObj.guidZ > 0 ? `axiom_${valueObj.guidZ}` : "root" }`;
            const lhsStringArray = convertBitstream2tokens ({ proofStepZ: valueObj.lhsZ, maskSizeZ: maskSizeZ });
            const rhsStringArray = convertBitstream2tokens ({ proofStepZ: valueObj.rhsZ, maskSizeZ: maskSizeZ });
            proofArray.push ( `${ lhsStringArray.join (' ') } = ${ rhsStringArray.join (' ') }, ${ phraseString }`);
        });

        resultArray.push (proofArray.join ('\n'), 'Q.E.D.');
    } else {
        resultArray.push ('No proof found.');
        console.info ("No proof found.");
    }

    console.info (`Total runtime: ${totalTimeZ} Milliseconds`);
    resultArray.push (`Total runtime: ${totalTimeZ} Milliseconds`);

    codeArea.value = resultArray.join('\n\n');

} // end main

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