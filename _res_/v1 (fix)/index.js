/*

  AUTHOR
      Seagat2011 www.gitub.com/Seagat2011
      eterna.cmu.edu/web/player/90270/
      fold.it/port/user/1992490

  VERSION
      Major.Minor.Bugfix.Patch
      11.0.0.0

  DESCRIPTION
    Theorem prover written in HTML and JavaScript (An E-normalization to normal form, term-rewriting system)

  UPDATED
      +Improved ProofComplete search performance
      +Prove via Auto functionality added (PASS)
      +Axiom._eval => Axiom._reduce
      +Axiom.{_reduce,_expand} eventListener(s)
      +solutionEditor made contentEditable
      +Prove via Reduce functionality added (PASS)
      +Prove via Expand functionality added (PASS)
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

var g_Solution = []
var g_code = []
var g_GUID = 0
var g_history = {}
var g_origin = "*"
var g_axiomSTACK=[]
var g_axiomLibrary=new Worker(URL.createObjectURL(new Blob( [cblock], {type:'text/javascript'} )))
g_axiomLibrary.onmessage=function(e){
    if(e.data._solved){
        //console.info('g_axiomLibrary.onmessage:',e.data._stack)
        solutionEditor.innerHTML=e.data._stack.txt.join('<br>')
        self.terminate()
    }
}
g_axiomLibrary.onerror=function(e){
    //console.info('g_axiomLibrary.onerror:', JSON.stringify(e,' ',2) )
    solutionEditor.innerText=JSON.stringify(e,' ',2)
}

function reset(partial){
  g_Solution = []
  g_history = {}
  g_code._resetRound()
  /*
  if(!partial && g_code.init()){
    g_code.build()
  }
  */
  g_code.solutionEditor.clearHTMLWindow()
  g_code.solutionEditorR.clearHTMLWindow()
}
function SymbolsViewer(action){
    if(action){
        solutionEditor.hideHTMLWindow()
        solutionEditorR.showHTMLWindow()
    } else {
        solutionEditor.showHTMLWindow()
        solutionEditorR.hideHTMLWindow()
    }
}
function Solve(INDIR){
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
  g_axiomLibrary.postMessage({
    INIT:g_axiomSTACK,
    Proof:g_code.Theorem.lemma,
    indir:INDIR })
  console.clear()
}