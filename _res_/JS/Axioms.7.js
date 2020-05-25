/*

  TITLE:
  Axioms.js

  AUTHOR: Seagat2011
  http://eterna.cmu.edu/web/player/90270/
  http://fold.it/port/user/1992490

  VERSION:
  Major.Minor.Release.Build
  1.0.0.0

  DESCRIPTION:
  Main (math) operations interface to euclid and its components

  UPDATED
  +Scoping functionality

  STYLEGUIDE:
  http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

  REFERENCES:
  There are two kinds of EQUALITIES:
  1. AXIOMATIC: 1 + 1 = 2
  2. LEMMA SUBSTITUTIONS: 1 <== 1/1
  Lemma substitutions (can) introduce recursions, stack overflows, and bugs

  SCRIPT TYPE:
  Euclid Tool

*/

function _AXIOM_(){
    var self = this
    var args = arguments[0]
    args.forEach(function(u){
        self[u] = args[u]
    })
    self._criteria=[[,],[,]] // callback array [ORs[ANDs,...],...] for Axioms (Turing Complete) //
    self._update = function(){
        var args = arguments[0]
        args.forEach(function(w){
            self[w] = args[w]
            return w
        })
    }
    self._reduce = function(e){
        var u = e.data
        if(u.source.startsWith("axiom") && self._guid.startsWith("axiom") && self._axiom && self._basenet && (u.source != self._guid) && u.indir.match(/Reduce|Auto/)){
            var val = u.val
            self._subnetFOUND = false
            var ProofFailed = false
            if(self._isOnline && !(val in g_history) && !(val in self._history) ){
                var val = u.val
                var tmp = [...val.split(/\s+/)]
                var Proof = [...val.split(/\s+/)]
                var vkeys = []
                var tmpHTML = {
                    pre:[...val.split(/\s+/)],
                    post:[...val.split(/\s+/)] }
                var alhs = self._axiom.split(/\s+/)
                var arhs = self._basenet.split(/\s+/)
                var jdx = 0
                tmp.map(function(tok,idx,me){
                    if(tok == "="){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,alhs,jdx)){
                        vkeys.push(idx)
                        if(++jdx==alhs.length){
                            g_code._passRound()
                            self._subnetFOUND = true
                            vkeys.map(function(kdx){
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                Proof[kdx] = null
                            })
                            tmpHTML.post[idx] = arhs.map(function(atok){ return (atok + self._id.addTAG("sub")) }).join(" ")
                            jdx=0
                            vkeys = []
                            Proof[idx] = arhs.join(" ")
                        }
                    }
                    return tok
                });
                // Failed? Try lemma substitution! //
                if(self._subnetFOUND == false){
                    postMessage({ source:'rewrite',_axiom:self._axiom,_basenet:self._basenet,_id:self._id,val:Proof.join(" "),indir:u.indir,mode:'Reduce' },g_origin)
                } else if(self._subnetFOUND){
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        var solutionComplete = Proof.solutionComplete("Reduce")
                        self._history[val] = true
                        g_history[val] = true // comment-out to view other partial-solutions //
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        if(solutionComplete){
                            self._solutionEditor.appendlog(Proof.join(" ")+solutionComplete)
                        } else {
                            postMessage({ source:self._guid,val:Proof.join(" "),indir:u.indir },g_origin)
                        }
                        console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<br><br>/,"")}`)
                    } else { // Solution Found //
                        e.stopPropagation()
                    }
                }
            }
            if(u.indir=='Auto'){
                clearTimeout(g_code.activeThread)
                g_code.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        g_code._resetRound()
                        self._solutionEditor.appendlog("<br>========( Reduce )=========<br>========( Expand )=========<br>")
                        reset("partial")
                        console.log("Prove via Reduce failed: Now attempting Expand...")
                        postMessage({ source:"axiomROOT",val:g_code.Theorem.lemma,indir:"Expand" },g_origin)
                    }
                },10)
            }
        }
    }
    self._expand = function(e){
        var u = e.data
        if(u.source.startsWith("axiom") && self._guid.startsWith("axiom") && self._axiom && self._basenet && (u.source != self._guid) && u.indir.match(/Expand/)){
            var val = u.val
            self._subnetFOUND = false
            if(self._isOnline && !(val in g_history) && !(val in self._history) ){
                var val = u.val
                var tmp = [...val.split(/\s+/)]
                var Proof = [...val.split(/\s+/)]
                var vkeys = []
                var tmpHTML = {
                    pre:[...val.split(/\s+/)],
                    post:[...val.split(/\s+/)]
                }
                var alhs = self._axiom.split(/\s+/)
                var arhs = self._basenet.split(/\s+/)
                var jdx = 0
                tmp.map(function(tok,idx,me){
                    if(tok == "="){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,arhs,jdx)){
                        vkeys.push(idx)
                        if(++jdx==arhs.length){
                            self._subnetFOUND = true
                            vkeys.map(function(kdx){
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                Proof[kdx] = null
                            })
                            tmpHTML.post[idx] = alhs.map(function(atok){ return (atok + self._id.addTAG("sub")) }).join(" ")
                            Proof[idx] = alhs.join(" ")
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                // Failed? Try lemma substitution! //
                if(self._subnetFOUND == false){
                    postMessage({ source:'rewrite',_axiom:self._axiom,_basenet:self._basenet,_id:self._id,val:Proof.join(" "),indir:u.indir,mode:'Expand' },g_origin)
                } else if(self._subnetFOUND){
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        var solutionComplete = Proof.solutionComplete("Expand")
                        self._history[val] = true
                        g_history[val] = true // comment-out to view other partial-solutions //
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        if(solutionComplete){
                            self._solutionEditor.appendlog(Proof.join(" ")+solutionComplete)
                        } else {
                            postMessage({ source:self._guid,val:Proof.join(" "),indir:u.indir },g_origin)
                        }
                        console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<br><br>/,"")}`)
                    } else { // Solution Found //
                        e.stopPropagation()
                    }
                }
            }
        }
    }
    self._lemmaGovernor = function(e){
        var u = e.data
        if(u.source.startsWith("rewrite") && self._guid.startsWith("lemma") && self._axiom && self._basenet){
            var val = u.val
            self._subnetFOUND = false
            if(self._isOnline && !(val in g_history) && !(val in self._history) ){
                var stream = val.split(/\s+/)
                var id = u._id
                var mode = u.mode
                var from = self._axiom.split(/\s+/)
                var to = self._basenet.split(/\s+/)
                var tmp = [];
                var buff = [];
                var intranet = [];
                var vkeys = [];
                // iff SUCCESS //
                var tmpHTML = {
                    pre:[...from.map((u,i,me)=>{ return u+self._id.addTAG('sub')})],
                    post:[...to.map((u,i,me)=>{ return u+self._id.addTAG('sub')})],
                }
                var j=0
                var rewrite = `lemma_${ id } ==> ${ val }`
                if(rewrite in g_history)
                    return
                g_history[rewrite] = true
                // attempt a novel axiom rewrite //
                u._axiom && u._axiom.split(/\s+/).map((v,i,me)=>{
                    if(v!=from[j]){
                        intranet.push(v)
                    } else if(v==from[j]) {
                        vkeys.push(j)
                        if(++j==from.length){
                            buff=[];
                            if(typeof(to)==="object"){
                                tmp.push(...to)
                            } else {
                                tmp.push(to)
                            }
                            !self._subnetFOUND && (self._subnetFOUND=true);
                            vkeys = []
                            j=0
                        } else {
                            buff.push(v)
                        }
                    }
                    return v
                })
                if(buff.length)
                    tmp.push(buff.join(' '))
                buff=[];
                // now try a novel proofstep using the axiom //
                if(self._subnetFOUND && !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                    intranet = [...intranet.length ? intranet.push(...tmp) : tmp]
                    self._solutionEditor.appendlog('*** Lemma *** '+tmpHTML.pre.join(" ")+' = '+u._basenet)
                    self._solutionEditor.appendlog('*** Lemma *** '+tmpHTML.post.join(" ")+' = '+u._basenet)
                    var tmp000 = intranet.join(' ').split(/\s+=\s+/)
                    var guid = g_code.push(new _AXIOM_
                        ({
                            _guid:"lemma_"+id,
                            _id:id,
                            _axiom:(tmp000.length>1) ? tmp000[1] : tmp000[0],
                            _basenet:(tmp000.length>1) ? tmp000[0] : u._basenet,
                            _bidirectional:self._bidirectional,
                            _stack:[],
                            _history:{},
                            _isOnline:true,
                            _false:"68934A3E9455FA72420237EB05902327",
                            _basenetFOUND:"68934A3E9455FA72420237EB05902327",
                            _solutionEditor:g_code.solutionEditor
                        })
                    );
                    postMessage({ source:('axiom_rewrite'+guid),val:val,indir:u.indir },g_origin)
                }
                // test: axiom <==> basenet //
                if(self._bidirectional) {

                }
            }
        }
    }
    self._auto = function(e){
    }
    self._balance = function(e){
    }
    self._reduce_stepwise = function(){
    }
    self._expand_stepwise = function(){
    }
    self._scope_satisfied = function(etok,lhs,li,rhs,ri){
        var i = 1
        var end_scope = { "(":")", "{":"}" }
        var sat = true
        if(lhs[li] != rhs[ri]){
            sat = false
        } else if(etok in end_scope) {
            if(((li+i) in lhs) && ((ri+i) in rhs)){
                var ltok = lhs[li+i]
                var rtok = rhs[ri+i]
                var I = rhs.length // Math.min(lhs.length,rhs.length) //
                etok = end_scope[etok]
                while(i++<I){
                    if(ltok!=rtok){
                        sat = false
                        break
                    }
                    if(rtok == etok){
                        break
                    }
                    //i++
                    ltok = lhs[li+i]
                    rtok = rhs[ri+i]
                }
            } else {
                sat = false
            }
        } // test(etok) //
        return sat
    }
  //addEventListener("message",self._auto)
  //addEventListener("message",self._balance)
  addEventListener("message",self._reduce)
  addEventListener("message",self._expand)
  addEventListener("message",self._lemmaGovernor)
}