
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
    Add async support

    STYLEGUIDE:
    http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

    EXAMPLE:
    const ProofStatementA = [
        // axioms and lemmas
        "1 + 1 = 2",
        "2 + 2 = 4"
        // prove
        1 + 2 + 1 = 4
    ];

    SCRIPT TYPE:
    Euclid Tool

*/

const ProofStatementsA = [
    // axioms and lemmas
    "1 + 1 = 2",
    "2 + 2 = 4",
    // prove
    "1 + 2 + 1 = 4",
]

let QED;
let guidZ = 1n; // 0n reserved (AXIOM ROOT)
let uuidZ = 0n;
let maskSizeZ = 0n;
let AxiomsArray = [];
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
let tokenLibraryD = {};
let lhsExpandProofFoundFlag;
let lhsReduceProofFoundFlag;
let rhsExpandProofFoundFlag;
let rhsReduceProofFoundFlag;
let tokenDelimeterRE = new RegExp ("\\s+","g");
let tokenOperatorsRE = new RegExp ("[<~]?=+>?");

class AxiomClass extends Object {
    constructor () {
        super ();

        this.guidZ = null;
        this.lhsZ = 0n;
        this.rhsZ = 0n;
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

function initCallGraphs ({
    axioms1C
    , resultObj: { axioms2C, _resultObj } = {}
    , stackA
}) {
    if (_resultObj == null) return;

    const retArray = [
        { isLHS: true, isExpand: true, values: _resultObj._lhsExpand },
        { isLHS: true, isExpand: false, values: _resultObj._lhsReduce },
        { isLHS: false, isExpand: true, values: _resultObj._rhsExpand },
        { isLHS: false, isExpand: false, values: _resultObj._rhsReduce }
    ]
    .forEach(({ isLHS, isExpand, values }) => {
        if (!values?.length) return;

        axioms1C[`${isLHS ? '_lhs' : '_rhs'}${isExpand ? 'Expand' : 'Reduce'}CallGraph`][axioms2C.guidZ] = true;            
    });
} // end initCallGraphs

function rewriteProofstepF({
    axioms1C    
    , resultObj: { axioms2C, resultObj: _resultObj } = {}
    , stackA
}) {
    if (_resultObj == null) return;

    const operations = [
        { isLHS: true, isExpand: true, values: _resultObj._lhsExpand },
        { isLHS: true, isExpand: false, values: _resultObj._lhsReduce },
        { isLHS: false, isExpand: true, values: _resultObj._rhsExpand },
        { isLHS: false, isExpand: false, values: _resultObj._rhsReduce }
    ];

    const resultsA = operations.map(({ isLHS, isExpand, values }) => {
        if (!values?.length) return false;

        let currentProofChain = [...stackA];
        for (let valueZ of values) {
            let proofStep = new ProofStepObjectClass();

            proofStep.guidZ = axioms2C.guidZ;
            proofStep[isLHS ? 'lhsZ' : 'rhsZ'] = valueZ;
            proofStep[isLHS ? 'rhsZ' : 'lhsZ'] = isLHS ? axioms2C.rhsZ : axioms2C.lhsZ;
            proofStep.rewriteOpcodeZ = rewriteOpcodesO[`_${isLHS ? 'lhs' : 'rhs'}${isExpand ? 'Expand' : 'Reduce'}`];

            const proofFound = (proofStep.lhsZ === proofStep.rhsZ);
            currentProofChain.push(proofStep);

            rewriteQueue.push(currentProofChain);

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

    let fromOffsetZ = (fromResolutionZ - maskSizeZ);
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

    const proofStepResolutionStartOffsetZ = (proofStepResolutionZ - maskSizeZ) + bitsRemainingZ;
    const fromResolutionStartOffsetZ = (fromResolutionZ - maskSizeZ);
    const fromResolutionResetZ = (fromResolutionZ - maskSizeZ);
    const toResolutionStartOffsetZ = toResolutionZ + (maskSizeZ - toOffsetBitsRemainingZ);

    for (let ii = proofStepResolutionStartOffsetZ; ii >= 0n; ii -= maskSizeZ) {
        const chunk = (proofStepZ >> ii) & chunkMask;
        const chunkFrom = (fromZ >> fromOffsetZ) & chunkMask;

        if (chunk === chunkFrom) {
            if (fromOffsetZ > 0n) {
                fromOffsetZ -= maskSizeZ;
            } else {
                fromOffsetZ = fromResolutionResetZ;
                resultZ = (resultZ << toResolutionStartOffsetZ) | toZ;
                const intermediateOffsetZ = ii;

                const intermediateOffsetMaskZ = (1n << intermediateOffsetZ) - 1n;

                const intermediateRewriteZ = (resultZ << intermediateOffsetZ) | (proofStepZ & intermediateOffsetMaskZ);

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

    let _resultObj = {
        _lhsExpand: false
        , _lhsReduce: false
        , _rhsExpand: false
        , _rhsReduce: false
    };

    _resultObj._lhsExpand = replaceBitfieldsInProofStepBigEndian ({
        proofStepZ: axioms1C.lhsZ
        , maskSizeZ: maskSizeZ
        , fromZ: axioms2C.rhsZ
        , toZ: axioms2C.lhsZ
        , firstRewriteOnlyFlag: firstRewriteOnlyFlag })

    , _resultObj._lhsReduce = replaceBitfieldsInProofStepBigEndian ({
        proofStepZ: axioms1C.lhsZ
        , maskSizeZ: maskSizeZ
        , fromZ: axioms2C.lhsZ
        , toZ: axioms2C.rhsZ
        , firstRewriteOnlyFlag: firstRewriteOnlyFlag })

    , _resultObj._rhsExpand = replaceBitfieldsInProofStepBigEndian ({
        proofStepZ: axioms1C.rhsZ
        , maskSizeZ: maskSizeZ
        , fromZ: axioms2C.rhsZ
        , toZ: axioms2C.lhsZ
        , firstRewriteOnlyFlag: firstRewriteOnlyFlag })

    , _resultObj._rhsReduce = replaceBitfieldsInProofStepBigEndian ({
        proofStepZ: axioms1C.rhsZ
        , maskSizeZ: maskSizeZ
        , fromZ: axioms2C.lhsZ
        , toZ: axioms2C.rhsZ
        , firstRewriteOnlyFlag: firstRewriteOnlyFlag }) ;

    return { axioms2C, _resultObj };

} // end compareAxioms

function processAxioms ({
    axiomsA
    , maskSizeZ
    , firstRewriteOnlyFlag = false
    , stackA = []
    , cb = null
}) {
    axiomsA.forEach(axioms1C => {
        AxiomsArray
        .map(axioms2C =>
            compareAxioms({
                axioms1C: axioms1C,
                axioms2C: axioms2C,
                maskSizeZ: maskSizeZ,
                firstRewriteOnlyFlag: firstRewriteOnlyFlag
            })
        )
        .forEach(result => cb({
            axioms1C: axioms1C,
            resultObj: result,  // contains { axioms2C, _resultObj }
            stackA: stackA
        }))
    });
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
    return proofStatementsA.map ((valueS, indexZ, thisArrayA) => {
        let axiomObj = new AxiomClass ();

        axiomObj.guidZ = indexZ < thisArrayA.length - 1 ? guidZ++ : 0n;

        valueS
            // tokens
            .split (tokenDelimeterRE)
            // finalize token library, maskSizeZ calibration
            .map ((thatValueS, thatIndexZ, thatArrayA) => {
                if (!tokenLibraryD[thatValueS]) {
                    tokenLibraryD[thatValueS] = 1n << uuidZ++;
                    maskSizeZ++;
                }
                return thatValueS;
            });

        return axiomObj;
    })
    // map tokens to values
    .map ((axiomObj, thatIndexZ, thatArrayA) => {
        let swapSubnetsFlag;
        proofStatementsA[thatIndexZ]
            .split  (tokenDelimeterRE)
            .forEach ((thatValueS, thatIndexZ, thatArrayA) =>{
                if (thatValueS.match (tokenOperatorsRE)) {
                    swapSubnetsFlag = true;
                } else if (!swapSubnetsFlag) {
                    axiomObj.lhsZ = (axiomObj.lhsZ << maskSizeZ) | tokenLibraryD[thatValueS];
                } else {
                    axiomObj.rhsZ = (axiomObj.rhsZ << maskSizeZ) | tokenLibraryD[thatValueS];
                }
            });

        return axiomObj;
    })
    // lhs > rhs
    .map ((axiomObj, thatIndexZ, thatArrayA) => {
        const lhsGreaterFlag = (axiomObj.lhsZ >= axiomObj.rhsZ);

        axiomObj.lhsZ = lhsGreaterFlag ? axiomObj.lhsZ : axiomObj.rhsZ ;
        axiomObj.rhsZ = lhsGreaterFlag ? axiomObj.rhsZ : axiomObj.lhsZ ;

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

    const I = AxiomsArray.length;
    const II = AxiomsArray.length * 2 - 1;

    // 2-pass as acting src and targ
    for (let i = 0; i < II; ++i){
        const ii = (i < I ? i : I - i%I - 2) ;
        processAxioms ({
            axiomsA: [AxiomsArray[ii]]
            , maskSizeZ: maskSizeZ
            , firstRewriteOnlyFlag: firstRewriteOnlyFlag
            , stackA: stackA
            , cb: cb });
    }

} // end initAxiomCallGraphs

function main () {

    AxiomsArray = initAxiomsArrayF ({ proofStatementsA: ProofStatementsA });

    initAxiomCallGraphs ({
        axiomsA: AxiomsArray
        , maskSizeZ: maskSizeZ
        , firstRewriteOnlyFlag: true
        , stackA: []
        , cb: initCallGraphs });

    const theoremA = AxiomsArray.pop (); // Theorem is the last element!

    rewriteQueue.push ([theoremA]);

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

    } while (rewriteQueue.length && !ProofFoundFlag);

    const endTimeZ = performance.now ();

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