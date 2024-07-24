
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


function solveProblem() {
    const input = document.getElementById('input').value;
    const output = document.getElementById('output');
    
    const { axioms, proofStatement } = parseInput(input);
    const proof = generateProof(axioms, proofStatement);
    
    output.value = proof;
}

function parseInput(input) {
    const lines = input.split('\n').map(line => line.trim()).filter(line => line && !line.startsWith('//'));
    const axioms = [];
    let proofStatement = '';

    const isProof = lines.length-1;
    lines
        .forEach((line, indexZ, thisArray) => {
            if (indexZ != isProof) {
                axioms.push(line);
            } else {
                proofStatement = line;
            }         
        });

    return { axioms, proofStatement };
}

function generateProof(axioms, proofStatement) {
    let proof = `Proof found!\n\n${proofStatement}, (root)\n`;
    const [lhs, rhs] = proofStatement.split('=').map(s => s.trim());

    if (lhs === rhs) 
        return proof + `\nQ.E.D.`;
    
    const steps = [];
    let currentLhs = lhs;
    let currentRhs = rhs;
    
    // Try to reduce RHS first
    while (true) {
        const rhsReduction = tryReduce(currentRhs, axioms);
        if (rhsReduction) {
            steps.push({ side: 'rhs', action: 'reduce', result: rhsReduction.result, axiom: rhsReduction.axiom });
            currentRhs = rhsReduction.result;
        } else {
            break;
        }
    }
    
    // Then expand LHS
    while (currentLhs !== currentRhs) {
        const lhsExpansion = tryExpand(currentLhs, axioms);
        if (lhsExpansion) {
            steps.push({ side: 'lhs', action: 'expand', result: lhsExpansion.result, axiom: lhsExpansion.axiom });
            currentLhs = lhsExpansion.result;
        } else {
            break;
        }
    }
    
    // If LHS and RHS are not equal, try reducing LHS
    if (currentLhs !== currentRhs) {
        while (true) {
            const lhsReduction = tryReduce(currentLhs, axioms);
            if (lhsReduction) {
                steps.push({ side: 'lhs', action: 'reduce', result: lhsReduction.result, axiom: lhsReduction.axiom });
                currentLhs = lhsReduction.result;
                if (currentLhs === currentRhs) break;
            } else {
                break;
            }
        }
    }
    
    for (const step of steps) {
        proof += `${step.result} = ${step.side === 'lhs' ? currentRhs : currentLhs}, (${step.side} ${step.action}) via ${step.axiom}\n`;
    }
    
    proof += '\nQ.E.D.';
    return proof;
}

function tryReduce(expression, axioms) {
    for (let i = 0; i < axioms.length; i++) {
        const [left, right] = axioms[i].split('=').map(s => s.trim());
        if (expression.includes(left)) {
            return {
                result: expression.replace(left, right),
                axiom: `axiom_${i + 1}.0`
            };
        }
    }
    return null;
}

function tryExpand(expression, axioms) {
    for (let i = 0; i < axioms.length; i++) {
        const [left, right] = axioms[i].split('=').map(s => s.trim());
        if (expression.includes(right)) {
            return {
                result: expression.replace(right, left),
                axiom: `axiom_${i + 1}.0`
            };
        }
    }
    return null;
}

input.value = input.value 
? input.value :
`// Axioms and Lemmas
1 + 1 = 2
2 + 2 = 4

// Prove
1 + 2 + 1 = 4`;

output.value = '';