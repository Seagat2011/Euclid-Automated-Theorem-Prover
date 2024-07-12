
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

    UPDATES
    Add FastForward support

    TODO
    Add Multi-threaded support via iinline Web Workers
    Add async/await support

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

const ProofStatementsA = [
    // Axioms and Lemmas
    "1 + 1 = 2",
    "2 + 2 = 4",
    // Theorem to prove
    "1 + 2 + 1 = 4",
]

let QED;
let guidZ = 1n; // 0n reserved (AXIOM ROOT)
let uuidZ = 0n;
let maskSizeZ = 0n;
let AxiomsArray = [];
let AxiomsArrayH = {}; // quick lookup
let ProofFoundFlag;
let fastForwardQueue = {};
let rewriteQueue = [];
const rewriteOpcodesO = {
    _lhsExpand: 1n,
    _lhsReduce: 2n,
    _rhsExpand: 3n,
    _rhsReduce: 4n,
    _lhsFastForwaard: 5n,
    _rhsFastForward: 6n,
};
let tokenLibraryMap = new Map ();
let lhsExpandProofFoundFlag;
let lhsReduceProofFoundFlag;
let rhsExpandProofFoundFlag;
let rhsReduceProofFoundFlag;
let tokenDelimeterRE = new RegExp ("\\s+","g");
let tokenOperatorsRE = new RegExp ("[<~]?=+>?");
let globalTime = 0;
let globalTimeRecord = new Map ();

class AxiomClass extends Object {
    constructor () {
        super ();

        this.guidZ = null;
        this.lhsZ = 0n;
        this.rhsZ = 0n;
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

function replaceBitfieldsInProofStepBigEndian ({
    proofStepZ
    , maskSizeZ
    , fromZ
    , toZ
    , firstRewriteOnlyFlag = false 
}) {    

    clock ({ valueS: "replaceBitfieldsInProofStepBigEndian" });

    const fromResolutionZ = _resolutionOf ({ valueZ: fromZ });
    const proofStepResolutionZ = _resolutionOf ({ valueZ: proofStepZ });

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
    const toResolutionZ = _resolutionOf ({ valueZ: toZ });

    //let fromOffsetZ = (fromResolutionZ - maskSizeZ);
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

    const lhsCallGraphFlag = AxiomsArrayH[axioms1C.guidZ]._lhsCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;
    const rhsCallGraphFlag = AxiomsArrayH[axioms1C.guidZ]._rhsCallGraph [axioms2C.guidZ] != null || firstRewriteOnlyFlag;

    if (lhsCallGraphFlag) {
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
    }

    if (rhsCallGraphFlag) {
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
    }

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

function _resolutionOf ({ valueZ }) {
    const I = BigInt (valueZ.toString (2).length);

    return I;
} // end _resolutionOf

function _lastElementOf ({ valueA }) {
    let ret;
    const ii = valueA.length - 1;

    if (valueA[ii]) {
        ret = valueA[ii];
    }

    return ret;
} // end _lastElementOf

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
    proofStatementsA.forEach (statement => {
        statement.split (tokenDelimeterRE).forEach (token => {
            if (!tokenLibraryMap.has (token)) {
                tokenLibraryMap.set (token, 1n << uuidZ++);
                maskSizeZ++;
            }
        });
    });

    // Second pass: create and populate axiom objects
    return proofStatementsA.map ((statement, indexZ) => {
        const axiomObj = new AxiomClass ();
        axiomObj.guidZ = indexZ < proofStatementsA.length - 1 ? BigInt (indexZ + 1) : 0n;

        let swapSubnetsFlag = false;
        let lhsZ = 0n;
        let rhsZ = 0n;

        statement.split (tokenDelimeterRE).forEach (token => {
            if (token.match (tokenOperatorsRE)) {
                swapSubnetsFlag = true;
            } else {
                const tokenValue = tokenLibraryMap.get (token);
                if (!swapSubnetsFlag) {
                    lhsZ = (lhsZ << maskSizeZ) | tokenValue;
                } else {
                    rhsZ = (rhsZ << maskSizeZ) | tokenValue;
                }
            }
        });

        // Ensure lhs > rhs for proper expand/reduce operation
        if (lhsZ >= rhsZ) {
            axiomObj.lhsZ = lhsZ;
            axiomObj.rhsZ = rhsZ;
        } else {
            axiomObj.lhsZ = rhsZ;
            axiomObj.rhsZ = lhsZ;
        }

        // Catalog for quick-lookup
        AxiomsArrayH[axiomObj.guidZ] = axiomObj;

        clock ({ valueS: 'initAxiomsArrayF' })

        return axiomObj;
    });
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

function main () {

    AxiomsArray = initAxiomsArrayF ({ proofStatementsA: ProofStatementsA });

    initAxiomCallGraphs ({
        axiomsA: AxiomsArray
        , maskSizeZ: maskSizeZ
        , firstRewriteOnlyFlag: true
        , stackA: []
        , cb: initCallGraphs });

    const theoremA = _lastElementOf({ valueA: AxiomsArray }); // Theorem is the last element!

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

        const proofStepC = _lastElementOf ({ valueA: proofstackA });

        const _lhsFastKeyS = `lhs:${proofStepC.lhsZ}`;
        const _rhsFastKeyS = `rhs:${proofStepC.rhsZ}`;

        !fastForwardQueue[_lhsFastKeyS] && (fastForwardQueue[_lhsFastKeyS] = [...proofstackA]);
        !fastForwardQueue[_rhsFastKeyS] && (fastForwardQueue[_rhsFastKeyS] = [...proofstackA]);

        const _lhsFastKeySearchS = `rhs:${proofStepC.lhsZ}`;
        const _rhsFastKeySearchS = `lhs:${proofStepC.rhsZ}`;

        if (fastForwardQueue[_lhsFastKeySearchS]) {
            QED = [...proofstackA];

            fastForwardQueue[_lhsFastKeySearchS]
            .map ((valueZ, indexZ, thisArrayA) => {
                const _lhsFastKeyO = new ProofStepObjectClass ();

                _lhsFastKeyO.guidZ = valueZ.guidZ;
                _lhsFastKeyO.lhsZ = proofStepC.lhsZ;
                _lhsFastKeyO.rhsZ = valueZ.rhsZ;
                _lhsFastKeyO.rewriteOpcodeZ = rewriteOpcodesO._lhsFastForwaard;

                QED.push (_lhsFastKeyO);

                return valueZ;
            });

            ProofFoundFlag = true;

            break;
        }

        if (fastForwardQueue[_rhsFastKeySearchS]) {
            QED = [...proofstackA];

            fastForwardQueue[_rhsFastKeySearchS]
            .map ((valueZ, indexZ, thisArrayA) => {
                const _rhsFastKeyO = new ProofStepObjectClass ();

                _rhsFastKeyO.guidZ = valueZ.guidZ;
                _rhsFastKeyO.lhsZ = valueZ.lhsZ;
                _rhsFastKeyO.rhsZ = proofStepC.rhsZ;
                _rhsFastKeyO.rewriteOpcodeZ = rewriteOpcodesO._lhsFastForwaard;

                QED.push (_rhsFastKeyO);

                return valueZ;
            });

            ProofFoundFlag = true;

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

    if (QED) {
        console.info ("Proof found!", "\n", QED, "\n", "Q.E.D.");
    } else {
        console.info ("No proof found.")
    }

    console.info (`Total runtime: ${totalTimeZ} Milliseconds`)

} // end main

try   {
    main ();
} catch (e) {
    console.info (`An error occured: ${e}`);
}