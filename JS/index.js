/*

  AUTHOR
      Seagat2011 www.gitub.com/Seagat2011
      eterna.cmu.edu/web/player/90270/
      fold.it/port/user/1992490

  VERSION
      Major.Minor.Bugfix.Patch
      11.0.0.2

  DESCRIPTION
    Theorem prover written in HTML and JavaScript (An E-normalization to normal form, term-rewriting system)

  UPDATED
    +Negative proof assertions ~=
    +_AXIOM_.optimizeCallGraph
    +Improved ProofComplete search performance
    +Prove via Auto (PASS)
    +Axiom._eval => Axiom._reduce
    +Axiom.{_reduce,_expand} => eventListener(s)
    +solutionEditor => contentEditable
    +Prove via Reduce (PASS)
    +Prove via Expand (PASS)
    +scoping functionality
    +LibreOffice math library support
    -Axiom._eval eventListener

  NOTES:
    Term rewrites are performed with the aid of a compiler (ie. via LEMMA SUBSTITUTION); SEE TEST CASES

    Substitution methods:
    1. (direct) AXIOMATIC: 1 + 1 = 2
    2. (indirect) LEMMA SUBSTITUTION: 1 <==> 1/1
    Lemma substitutions rewrite axioms -- which can introduce recursion, stack overflow, and other bugs

  Ex. // Lemma substitution //

    { { a } raised { 2 } } plus { 2ab } plus { b raised { 2 } } <== ( { a } plus { b } ) raised { 2 }
    ( { a } plus { b } ) raised { 2 } minus { 2ab } = { c } raised { 2 } <== ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
    { { a } raised { 2 } } plus { 2ab } minus { 2ab } plus { b raised { 2 } } ==> { { a } raised { 2 } } plus { { b } raised { 2 } }
    ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
    Prove { { a } raised { 2 } } plus { { b } raised { 2 } } = { c } raised { 2 }

  REFERENCES

  COMPATIBILITY
    Chrome 53+

*/
const dispatchProofstepEvent = new CustomEvent('dispatchProofstep');
var g_global_message_queue = [];
var g_global_rewrite_cache = { 
      _lhs:{}
    , _rhs:{}
};
var g_Solution = []
var g_code = []
var g_GUID = 0
var g_history = {}
var g_origin = "*"
var g_SOLVED = ""

function reset(partial){
  g_Solution = [];
  g_history = {};
  g_global_rewrite_cache._lhs = {};
  g_global_rewrite_cache._rhs = {};
  if(!partial){
    g_code.empty();
  }
  g_code.solutionEditor.clear();
  g_code.solutionEditorR.clear();
}
function SymbolsViewer(action){
    if(action){
        solutionEditor.hide()
        solutionEditorR.show()
    } else {
        solutionEditor.show()
        solutionEditorR.hide()
    }
}
function Solve(INDIR){
    try{
        if(!g_code.init()){
            g_code.attachSourceEditor({
                edt:axmEditor,
                lib:libEditor,
                axm:axmEditor,
                solutionEditor:solutionEditor,
                solutionEditorR:solutionEditorR,
                lma:lemmaEditor })
        }
        reset()
        g_code.build()
        imgProgressBar.show()
        g_SOLVED=""
        postMessage({
            source:"axiomROOT",
            Proof:g_code.Theorem.lemma,
            indir:INDIR,
            _deepRewritesEnabled_Flag:false,
            ProofSUBKEY:g_code.Theorem.lemma.asPrimaryKey(),
            },g_origin);
        console.clear();
        if(!g_SOLVED){
          postMessage({
              source:"axiomROOT",
              Proof:g_code.Theorem.lemma,
              indir:INDIR,
              _deepRewritesEnabled_Flag:true,
              ProofSUBKEY:g_code.Theorem.lemma.asPrimaryKey(),
              },g_origin);
          console.clear();
        }
    } catch(e) {
       solutionEditor.innerText=[`Error: ${e.message}...`,e.stack.replace(/@/g,' >> ')].join('\n\n') 
    }
}
