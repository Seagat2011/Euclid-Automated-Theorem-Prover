
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
let AxiomCallGraph = {
    _lhsExpand: new Map (),
    _lhsReduce: new Map (),
    _rhsExpand: new Map (),
    _rhsReduce: new Map (),
};
let ProofFoundFlag;
let fastForwardQueue = {};
let rewriteQueue = new BigUint64Array();
let sessionRuntimeClockFlag; // debug only
const rewriteOpcodesO = {
    _lhsExpand: 1n,
    _lhsReduce: 2n,
    _rhsExpand: 3n,
    _rhsReduce: 4n,
};
const rewriteOpcodeZtoString = {
    [rewriteOpcodesO._lhsExpand]: "lhs expand",
    [rewriteOpcodesO._lhsReduce]: "lhs reduce",
    [rewriteOpcodesO._rhsExpand]: "rhs expand",
    [rewriteOpcodesO._rhsReduce]: "rhs reduce",
};
let globalTime = 0;
let globalTimeRecord = new Map ();
let tokenLibraryMap = new Map ();
let tokenLibraryInverseMap = new Map ();
let lhsExpandProofFoundFlag;
let lhsReduceProofFoundFlag;
let rhsExpandProofFoundFlag;
let rhsReduceProofFoundFlag;
let tokenDelimeterRE = new RegExp ("\\s+","g");
let tokenOperatorsRE = new RegExp ("[<~]?=+>?");
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
        this._lhsExpandCallGraph = new Map ();
        this._lhsReduceCallGraph = new Map ();
        this._rhsExpandCallGraph = new Map ();
        this._rhsReduceCallGraph = new Map ();
    }
} // end class AxiomClass

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

    let proofStep = [];

    proofStep.push (theoremA.lhsPrimaryKeyZ);
    proofStep.push (theoremA.rhsPrimaryKeyZ);
    proofStep.push (theoremA.guidZ);
    proofStep.push (0n);    /* rewriteOpcodeZ */
    proofStep.push (0n);    /* fastfowardFlag */
    
    rewriteQueue.push (proofStep);

    //clock ({ valueS: "main" });

    const startTimeZ = performance.now ();

    do {

        // read from (the top of) the rewriteQueue
        const proofStepC = rewriteQueue.pop ();

        rewriteSubnets ({ proofStepC: proofStepC });

        if (ProofFoundFlag){
            const proofVerifiedFlag = proofFoundVerifiedF ();
            if (proofVerifiedFlag){
                break;
            } else {
                ProofFoundFlag = false;
                QED = [];
            }
        }

        //clock ({ valueS: "main" });

    } while (rewriteQueue.length);

    const endTimeZ = performance.now ();

    //clock ({});

    const totalTimeZ = endTimeZ - startTimeZ;

    console.info (`Total runtime: ${totalTimeZ} Milliseconds`);
    codeArea.value += `\n\nTotal runtime: ${totalTimeZ} Milliseconds`;

    function proofFoundVerifiedF (){

        let resultArray = [];

        let proofVerifiedFlag;

        let proofStatusFlag = "";
        let QED_Flag = "";

        if (!ProofFoundFlag && QED.length > 1){
            proofStatusFlag = "Partial-proof found.";
        } else if (ProofFoundFlag) {
            proofStatusFlag = "Proof found!";
            QED_Flag = "Q.E.D.";
        }

        if (proofStatusFlag) {
            resultArray.push (proofStatusFlag);
            console.info (proofStatusFlag, "\n", QED_Flag);

            let axiom1C;
            const offsetZ = 3;
            let offsetAddressZ = 5;
            const baseAddressZ = 5;
            const proofArray = [];

            QED.forEach ((
                _
                , indexZ
                , thisArray) => {
                if (indexZ == offsetAddressZ) {
                    // Handle other cases                    
                    const localGuidZ = thisArray[offsetAddressZ + 0];
                    const axiom2C = AxiomsArrayH [localGuidZ];
                    axiom1C.rewriteOpcodeZ = thisArray[offsetAddressZ + 1];
                    const localFastForwardFlag = (() => {
                        let u = '';
                        switch(thisArray[offsetAddressZ + 2]) {
                            case 1n:
                                u = '(lhs fast-forward)';
                                break;
                            case 2n:
                                u = '(rhs fast-forward)';
                                break;
                        }
                        return u;
                    })();
                    const { _axiom1C = axiom2C, _proofArray = [] }
                        = processProofStep (
                            axiom1C, 
                            axiom2C, 
                            maskSizeZ, 
                            localFastForwardFlag );

                    axiom1C = _axiom1C;
                    proofArray.push (..._proofArray);

                    offsetAddressZ += offsetZ;
                } else if (indexZ < 1) {
                    // Handle the root case
                    // thisArray[0]; // lhsPrimaryKeyZ
                    // thisArray[1]; // rhsPrimaryKeyZ
                    const axiom1CguidZ = thisArray[2];
                    // thisArray[3]; // rewriteOpcodeZ
                    // thisArray[4]; // fast-forwatd tag
                    const localAxiomObj = AxiomsArrayH[axiom1CguidZ];
                    axiom1C = {
                        lhsZ: localAxiomObj.lhsZ, 
                        rhsZ: localAxiomObj.rhsZ,
                        rewriteOpcodeZ: 0n, 
                    };
                    const lhsZ = axiom1C.lhsZ;
                    const rhsZ = axiom1C.rhsZ;
                    const lhsStringArray = convertBitstream2tokens ({ proofStepZ: lhsZ, maskSizeZ });
                    const rhsStringArray = convertBitstream2tokens ({ proofStepZ: rhsZ, maskSizeZ });
                    proofArray.push (`${lhsStringArray.join (' ')} = ${rhsStringArray.join (' ')}, (root)`);
                }
            }); // end QED.forEach

            resultArray.push (proofArray.join ('\n'), QED_Flag);

            function processProofStep (
                _localAxiom1C, 
                _localAxiom2C, 
                _localMaskSizeZ, 
                _localFastForwardFlag,
            ) {
                const _guidZ = _localAxiom2C.guidZ;
                let rewriteOpcodeZ = _localAxiom1C.rewriteOpcodeZ;
                let phraseString = [];
                let proofArray = [];

                let lhsStringArray = [];
                let rhsStringArray = [];
                let rewriteResultZArray = [];

                switch (rewriteOpcodeZ) {
                    case 1n: // lhsExpand
                    case 2n: // lhsReduce
                        phraseString.push (`(${rewriteOpcodeZtoString [rewriteOpcodeZ]}) via axiom_${_guidZ} ${_localFastForwardFlag}`);
                        rhsStringArray = convertBitstream2tokens ({ proofStepZ: _localAxiom1C.rhsZ, maskSizeZ: _localMaskSizeZ });
                        rewriteResultZArray = replaceBitfieldsInProofStepBigEndian ({
                            proofStepZ: _localAxiom1C.lhsZ,
                            maskSizeZ: _localMaskSizeZ,
                            fromZ: rewriteOpcodeZ === 1n ? _localAxiom2C.rhsZ : _localAxiom2C.lhsZ,
                            toZ: rewriteOpcodeZ === 1n ? _localAxiom2C.lhsZ : _localAxiom2C.rhsZ
                        });
                        break;
                    case 3n: // rhsExpand
                    case 4n: // rhsReduce
                        phraseString.push (`(${rewriteOpcodeZtoString [rewriteOpcodeZ]}) via axiom_${_guidZ} ${_localFastForwardFlag}`);
                        lhsStringArray = convertBitstream2tokens ({ proofStepZ: _localAxiom1C.lhsZ, maskSizeZ: _localMaskSizeZ });
                        rewriteResultZArray = replaceBitfieldsInProofStepBigEndian ({
                            proofStepZ: _localAxiom1C.rhsZ,
                            maskSizeZ: _localMaskSizeZ,
                            fromZ: rewriteOpcodeZ === 3n ? _localAxiom2C.rhsZ : _localAxiom2C.lhsZ,
                            toZ: rewriteOpcodeZ === 3n ? _localAxiom2C.lhsZ : _localAxiom2C.rhsZ
                        });
                        break;
                } // end if (rewriteOpcodeZ)

                rewriteResultZArray
                    .forEach ((valueZ, thatIndexZ, thatArray) => {
                        if (rewriteOpcodeZ === 1n || rewriteOpcodeZ === 2n) {
                            // lhs operations
                            _localAxiom1C.lhsZ = valueZ;
                            !proofVerifiedFlag && (proofVerifiedFlag = (_localAxiom1C.lhsZ == _localAxiom1C.rhsZ));
                            const newLhsStringArray = convertBitstream2tokens ({ proofStepZ: valueZ, maskSizeZ: _localMaskSizeZ });
                            proofArray.push (`${newLhsStringArray.join (' ')} = ${rhsStringArray.join (' ')}, ${phraseString [0]}`);
                        } else {
                            // rhs operations
                            _localAxiom1C.rhsZ = valueZ;
                            !proofVerifiedFlag && (proofVerifiedFlag = (_localAxiom1C.lhsZ == _localAxiom1C.rhsZ));
                            const newRhsStringArray = convertBitstream2tokens ({ proofStepZ: valueZ, maskSizeZ: _localMaskSizeZ });
                            proofArray.push (`${lhsStringArray.join (' ')} = ${newRhsStringArray.join (' ')}, ${phraseString [0]}`);
                        }
                    }); // end rewriteResultZArray.forEach

                return { _axiom1C: _localAxiom1C, _proofArray: proofArray };
            } // end processProofStep

        } else {
            resultArray.push ('No proof found.');
            console.info ("No proof found.");
        } // end if (proofStatusFlag)
        

        if (ProofFoundFlag && !proofVerifiedFlag) {
            resultArray[0] = "Partial-proof found";
            resultArray.pop (); // Q.E.D.
        }

        codeArea.value = resultArray.join ('\n\n');

        return proofVerifiedFlag;

    } // end proofFoundF

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
    PrimaryKeysMatchFlag = false;
    tokenLibraryMap = new Map ();
    tokenLibraryInverseMap = new Map ();
    sessionRuntimeClockFlag = false; // debug only
    lhsExpandProofFoundFlag = false;
    lhsReduceProofFoundFlag = false;
    rhsExpandProofFoundFlag = false;
    rhsReduceProofFoundFlag = false;
} // end resetProof

function initAxiomsArrayF ({ proofStatementsA = [] }) {

    //clock ({ valueS: "initAxiomsArrayF" });

    // First pass: build token library and calculate maskSizeZ
    let _proofStatementsA = [];

    proofStatementsA
        .split (newlinesRE)
            .forEach (statement => {
                if (/^[\w\{]/.test (statement)){
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

    maskSizeZ = resolutionOf ({ valueZ: LASTPRIME });

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
                        contentsZArray [i] = (contentsZArray [i] << maskSizeZ) | tokenValue;
                        primaryKeyZArray [i] *= tokenValue;
                    }
                });

            let _guid2PartZ = 0n;

            contentsZArray
                .forEach ((_, i, array) => {
                    for (let j = i + 1; j < array.length; j++) {
                        const lhsZ = array [i] >= array [j] ? array [i] : array [j];
                        const rhsZ = array [i] >= array [j] ? array [j] : array [i];
                        const lhsPkeyZ = array [i] >= array [j] ? primaryKeyZArray [i] : primaryKeyZArray [j] ;
                        const rhsPkeyZ = array [i] >= array [j] ? primaryKeyZArray [j] : primaryKeyZArray [i] ;
                        const visitedString = `${lhsZ}:${rhsZ}`;

                        if (!visitedMap.has (visitedString)) {
                            visitedMap.set (visitedString, true);
                            const axiomObj = new AxiomClass ();
                            axiomObj.guidZ = indexZ < thisArrayA.length - 1 ? `${_guidZ}.${_guid2PartZ++}` : 0n;

                            // Ensure lhs > rhs for proper expand/reduce operation
                            axiomObj.lhsZ = lhsZ;
                            axiomObj.rhsZ = rhsZ;
                            axiomObj.lhsPrimaryKeyZ = lhsPkeyZ;
                            axiomObj.rhsPrimaryKeyZ = rhsPkeyZ;

                            // Catalog for quick-lookup
                            AxiomsArrayH [axiomObj.guidZ] = axiomObj;

                            axiomObjArray.push (axiomObj);
                        }
                    }
                });

            _guidZ++;

        }); // end _proofStatementsA.forEach

    //clock ({ valueS: 'initAxiomsArrayF' })

    return axiomObjArray;

} // end initAxiomsArrayF

function processAxioms ({
    axiomsA,
    maskSizeZ,
    firstRewriteOnlyFlag = false,
    stackA = [],
    cb = null
}) {
    //clock ({ valueS: "processAxioms" });

    axiomsA.forEach (axioms1C => {
        AxiomsArray.forEach (axioms2C => {
            if (axioms1C.guidZ === axioms2C.guidZ) {
                return; // Skip comparison if GUIDs are the same
            }

            if (firstRewriteOnlyFlag && axioms2C.guidZ != 0n) {

                let _resultObj = {
                    _lhsExpand: false,
                    _lhsReduce: false,
                    _rhsExpand: false,
                    _rhsReduce: false
                };

                _resultObj._lhsExpand = axioms1C.lhsPrimaryKeyZ % axioms2C.rhsPrimaryKeyZ === 0n;
                _resultObj._lhsReduce = axioms1C.lhsPrimaryKeyZ % axioms2C.lhsPrimaryKeyZ === 0n;
                _resultObj._rhsExpand = axioms1C.rhsPrimaryKeyZ % axioms2C.rhsPrimaryKeyZ === 0n;
                _resultObj._rhsReduce = axioms1C.rhsPrimaryKeyZ % axioms2C.lhsPrimaryKeyZ === 0n;

                cb ({
                    axioms1C: axioms1C,
                    resultObj: { axioms2C, _resultObj },
                    stackA: stackA
                });

            }

        });
    });

    //clock ({ valueS: 'processAxioms' });

} // end processAxioms

function rewriteSubnets ({ proofStepC }) {

    if (updateProofFoundFlag ({ _proofStepC: proofStepC }))
        return;

    const fastForwardFlagAddress = proofStepC.length-1; 
    const rewriteOpcodeZAddress = proofStepC.length-2; 
    const guidZAddress = proofStepC.length-3;
    const localGuidZ = proofStepC[guidZAddress];
    const axiom2C = AxiomsArrayH[localGuidZ];
    
    //clock ({ valueS: "rewriteSubnets" });
    
    if (axiom2C._lhsExpandCallGraph.size > 0)
        rewriteSubnet_lhsExpand ({ _proofStepC: proofStepC, _subnets: axiom2C._lhsExpandCallGraph });
    if (axiom2C._lhsReduceCallGraph.size > 0)
        rewriteSubnet_lhsReduce ({ _proofStepC: proofStepC, _subnets: axiom2C._lhsReduceCallGraph });
    if (axiom2C._rhsExpandCallGraph.size > 0)
        rewriteSubnet_rhsExpand ({ _proofStepC: proofStepC, _subnets: axiom2C._rhsExpandCallGraph });
    if (axiom2C._rhsReduceCallGraph.size > 0)
        rewriteSubnet_rhsReduce ({ _proofStepC: proofStepC, _subnets: axiom2C._rhsReduceCallGraph });
    
    function rewriteSubnet_lhsExpand ({ _proofStepC, _subnets }) {
        if (ProofFoundFlag)
            return;

        const lhs = 0;
        const rhs = 1;
        const rhsFastForwardKeyS = `rhs:${_proofStepC[rhs]}`;
        !fastForwardQueue [rhsFastForwardKeyS]
            && (fastForwardQueue [rhsFastForwardKeyS] = [..._proofStepC]);
        for (let [localGuidZ, _] of _subnets) {
            const _axiom2C = AxiomsArrayH[localGuidZ];
            if (_proofStepC[lhs] % _axiom2C.rhsPrimaryKeyZ === 0n) {
                const newProofStepC = [..._proofStepC];
                newProofStepC.push (_axiom2C.guidZ);
                newProofStepC.push (rewriteOpcodesO._lhsExpand);
                newProofStepC.push (0n); // fastForward tag //
                newProofStepC[lhs] = newProofStepC[lhs] / _axiom2C.rhsPrimaryKeyZ * _axiom2C.lhsPrimaryKeyZ;
                const lhsFastForwardKeyS = `lhs:${newProofStepC[lhs]}`;
                !fastForwardQueue [lhsFastForwardKeyS]
                    && (fastForwardQueue [lhsFastForwardKeyS] = [...newProofStepC]);
                rewriteQueue.push (newProofStepC);
                updateProofFoundFlag ({ _proofStepC: newProofStepC });
            }
        }
    }

    function rewriteSubnet_lhsReduce ({ _proofStepC, _subnets }) {
        if (ProofFoundFlag)
            return;

        const lhs = 0;
        const rhs = 1;
        const rhsFastForwardKeyS = `rhs:${_proofStepC[rhs]}`;
        !fastForwardQueue [rhsFastForwardKeyS]
            && (fastForwardQueue [rhsFastForwardKeyS] = [..._proofStepC]);
        for (let [localGuidZ, _] of _subnets) {
            const _axiom2C = AxiomsArrayH[localGuidZ];
            if (_proofStepC[lhs] % _axiom2C.lhsPrimaryKeyZ === 0n) {
                const newProofStepC = [..._proofStepC];
                newProofStepC.push (_axiom2C.guidZ);
                newProofStepC.push (rewriteOpcodesO._lhsReduce);
                newProofStepC.push (0n); // fastForward tag //
                newProofStepC[lhs] = newProofStepC[lhs] / _axiom2C.lhsPrimaryKeyZ * _axiom2C.rhsPrimaryKeyZ;
                const lhsFastForwardKeyS = `lhs:${newProofStepC[lhs]}`;
                !fastForwardQueue [lhsFastForwardKeyS]
                    && (fastForwardQueue [lhsFastForwardKeyS] = [...newProofStepC]);
                rewriteQueue.push (newProofStepC);
                updateProofFoundFlag ({ _proofStepC: newProofStepC });
            }
        }
    }

    function rewriteSubnet_rhsExpand ({ _proofStepC, _subnets }) {
        if (ProofFoundFlag)
            return;

        const lhs = 0;
        const rhs = 1;
        const lhsFastForwardKeyS = `lhs:${_proofStepC[lhs]}`;
        !fastForwardQueue [lhsFastForwardKeyS]
            && (fastForwardQueue [lhsFastForwardKeyS] = [..._proofStepC]);
        for (let [localGuidZ, _] of _subnets) {
            const _axiom2C = AxiomsArrayH[localGuidZ];            
            if (_proofStepC[rhs] % _axiom2C.rhsPrimaryKeyZ === 0n) {
                const newProofStepC = [..._proofStepC];
                newProofStepC.push (_axiom2C.guidZ);
                newProofStepC.push (rewriteOpcodesO._rhsExpand);
                newProofStepC.push (0n); // fastForward tag //
                newProofStepC[rhs] = newProofStepC[rhs] / _axiom2C.rhsPrimaryKeyZ * _axiom2C.lhsPrimaryKeyZ;
                const rhsFastForwardKeyS = `rhs:${newProofStepC[rhs]}`;
                !fastForwardQueue [rhsFastForwardKeyS]
                    && (fastForwardQueue [rhsFastForwardKeyS] = [...newProofStepC]);
                rewriteQueue.push (newProofStepC);
                updateProofFoundFlag ({ _proofStepC: newProofStepC });
            }
        }
    }

    function rewriteSubnet_rhsReduce ({ _proofStepC, _subnets }) {
        if (ProofFoundFlag)
            return;

        const lhs = 0;
        const rhs = 1;
        const lhsFastForwardKeyS = `lhs:${_proofStepC[lhs]}`;
        !fastForwardQueue [lhsFastForwardKeyS]
            && (fastForwardQueue [lhsFastForwardKeyS] = [..._proofStepC]);
        for (let [localGuidZ, _] of _subnets) {
            const _axiom2C = AxiomsArrayH[localGuidZ];            
            if (_proofStepC[rhs] % _axiom2C.lhsPrimaryKeyZ === 0n) {
                const newProofStepC = [..._proofStepC];
                newProofStepC.push (_axiom2C.guidZ);
                newProofStepC.push (rewriteOpcodesO._rhsReduce);
                newProofStepC.push (0n); // fastForward tag //
                newProofStepC[rhs] = newProofStepC[rhs] / _axiom2C.lhsPrimaryKeyZ * _axiom2C.rhsPrimaryKeyZ;
                const rhsFastForwardKeyS = `rhs:${newProofStepC[rhs]}`;
                !fastForwardQueue [rhsFastForwardKeyS]
                    && (fastForwardQueue [rhsFastForwardKeyS] = [...newProofStepC]);
                rewriteQueue.push (newProofStepC);
                updateProofFoundFlag ({ _proofStepC: newProofStepC });
            }
        }
    }

    function updateProofFoundFlag ({ _proofStepC }) {
        if (ProofFoundFlag)
            return ProofFoundFlag;

        const lhs = 0;
        const rhs = 1;
        ProofFoundFlag = (_proofStepC[lhs] == _proofStepC[rhs]);

        if (ProofFoundFlag){
            QED = _proofStepC;
            return ProofFoundFlag;
        }

        const offsetZ = 3;
        const baseAddressZ = 4;
        let offsetAddressZ;
        const fastForwardTagAddress = 3;
        const lhsFastForwardTagZ = 1n;
        const rhsFastForwardTagZ = 2n;

        offsetAddressZ = baseAddressZ;
        const lhsMatchingFastForwardKeyS = `rhs:${ _proofStepC[lhs] }`;
        if (fastForwardQueue [lhsMatchingFastForwardKeyS]){
            QED = _proofStepC;
            QED[rhs] = QED[lhs];
            fastForwardQueue [lhsMatchingFastForwardKeyS]
                .forEach ((proofStepPropertyZ, indexZ, thisArray) => {
                    if ((indexZ > baseAddressZ)){
                        QED.push (indexZ != offsetAddressZ + fastForwardTagAddress 
                            ? proofStepPropertyZ 
                            : rhsFastForwardTagZ); /* (rhs fast-forward) */
                        if (indexZ == offsetAddressZ)
                            offsetAddressZ += offsetZ;
                    }
                });

                ProofFoundFlag = true;

            return ProofFoundFlag;
        }

        offsetAddressZ = baseAddressZ;
        const rhsMatchingFastForwardKeyS = `lhs:${ _proofStepC[rhs] }`;
        if (fastForwardQueue [rhsMatchingFastForwardKeyS]){
            QED = _proofStepC;
            QED[lhs] = QED[rhs];
            fastForwardQueue [rhsMatchingFastForwardKeyS]
                .forEach ((proofStepPropertyZ, indexZ, thisArray) => {
                    if ((indexZ > baseAddressZ)){
                        QED.push (indexZ != offsetAddressZ + fastForwardTagAddress 
                            ? proofStepPropertyZ 
                            : lhsFastForwardTagZ); /* (lhs fast-forward) */
                        if (indexZ == offsetAddressZ)
                            offsetAddressZ += offsetZ;
                    }
                });

                ProofFoundFlag = true;

            return ProofFoundFlag;
        }

        return false

    } // end updateProofFoundFlag

} // end rewriteSubnets

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
} // end //clock

function initCallGraphs ({
    axioms1C
    , resultObj
    , stackA
}) {

    if (isNotEmpty ({ targ: resultObj })) {
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

function isNotEmpty ({ targ }) {
    const resultFlag = Object.keys (targ).length > 0;
    return resultFlag;
} // end isNotEmpty

function convertBitstream2tokens ({ proofStepZ, maskSizeZ }) {

    //clock ({ valueS: "bitstream2tokens" });

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

    //clock ({ valueS: "replaceBitfieldsInProofStepBigEndian" });

    const fromResolutionZ = resolutionOf ({ valueZ: fromZ });
    const proofStepResolutionZ = resolutionOf ({ valueZ: proofStepZ });

    const subnetNotFoundFlag = (fromResolutionZ > proofStepResolutionZ);

    let ret = [];

    if (subnetNotFoundFlag)
        return ret;

    const _fastForwardKey = `${proofStepZ}:${fromZ}:${toZ}`;

    if (fastForwardQueue [_fastForwardKey]) {
        ret = fastForwardQueue [_fastForwardKey];

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

    //clock ({ valueS: 'replaceBitfieldsInProofStepBigEndian'});

    fastForwardQueue [_fastForwardKey] = [...ret];

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

    if (valueA [ii]) {
        ret = valueA [ii];
    }

    return ret;
} // end lastElementOf

function initAxiomCallGraphs ({
    axiomsA
    , maskSizeZ
    , firstRewriteOnlyFlag = true
    , stackA = []
    , cb = null
}) {

    //clock ({ valueS: "initAxiomCallGraphs" });

    const I = AxiomsArray.length;
    const II = AxiomsArray.length * 2 - 1;

    // 2-pass as acting src and targ
    for (let i = 0; i < II; ++i){
        const ii = (i < I ? i : I - i%I - 2) ;
        processAxioms ({
            axiomsA: [AxiomsArray [ii]]
            , maskSizeZ: maskSizeZ
            , firstRewriteOnlyFlag: true
            , stackA: stackA
            , cb: cb });
    }

    //clock ({ valueS: 'initAxiomCallGraphs'});

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
      if (isPrime (num)) {
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
        : '// Axioms and Lemmas\n1 + 1 = 2\n2 + 2 = 4\n\n// Theorem to prove\n1 + 2 + 1 = 4';

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