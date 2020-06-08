SYMP: Solve() Error : _AXIOM_ not defined... // function reset(){ ... g_code.empty() } //
      g_code.build()
      reset()
SOLU: reset()
      g_code.build()

SYMP: postMessage not received by _AXIOM_
SOLU: addEventListener("message",self._reduce)
      addEventListener("message",self._expand)

SYMP: opSTACK and u._subkey misaligned
SOLU: opSTACK.map((op,i,opme)=>{ var op=opSTACK.shift() ... }) => opSTACK.map((op,i,opme)=>{ ... return op })
      Object.prototype.asPrimaryKey=function(){ var x = ... } => Object.prototype.asPrimaryKey=function(){ ... var y=x.join(' ') ... }
      u._subkey => var subkey = u._subkey // Copy to local because u is still a GLOBAL PostMessage Object

SYMP: v10 lemmas not working
SOLU: PrimeFastCheck

SYMP: _AXIOM_ gets stuck in Proving loop (eg between axioms)
SOLU: _AXIOM_.optimizeCallGraph