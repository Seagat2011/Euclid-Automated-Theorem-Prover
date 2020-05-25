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
  Main (math) operational interface to Euclid and its components

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
    self._criteria=[[,],[,]] // callback array of [ORs[ANDs,...],[ANDs,...]...] for Axioms (Turing Complete) //
    self._update = function(){
        var args = arguments[0]
        args.forEach(function(w){
            self[w] = args[w]
            return w
        })
    }
    self._reduce = function(e){
        var u = e.data
        if(u.source.match(/axiom/) && self._guid.match(/axiom|lemma/) && self._subnet && self._supernet && (u.source != self._guid) && u.indir.match(/Reduce|Auto/)){
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
                var alhs = self._subnet.split(/\s+/)
                var arhs = self._supernet.split(/\s+/)
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
                            vkeys.map(function(kdx,ii){
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = arhs.map(function(atok){ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    Proof[kdx] = arhs.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                // Fail? Attempt lemma substitution //
                if(self._subnetFOUND == false){
                    postMessage({ source:'rewrite',_subnet:self._subnet,_supernet:self._supernet,_id:self._id,val:Proof.join(" "),indir:u.indir },g_origin)
                } else if(self._subnetFOUND){
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        var solutionComplete = Proof.solutionComplete("Reduce")
                        self._history[val] = true
                        g_history[val] = true // comment-out to view other partial-solutions //
                        if(self._stack.length){
                            self._solutionEditor.appendlog(self._stack.join('<br>'))
                            self._stack=[]
                        }
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        if(solutionComplete){
                            self._solutionEditor.appendlog(Proof.join(" ")+solutionComplete)
                        } else {
                            postMessage({ source:self._guid,val:Proof.join(" "),indir:u.indir },g_origin)
                        }
                        console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<br><br>/,"")}`)
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
        if(u.source.match(/axiom/) && self._guid.match(/axiom|lemma/) && self._subnet && self._supernet && (u.source != self._guid) && u.indir.match(/Expand/)){
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
                var alhs = self._subnet.split(/\s+/)
                var arhs = self._supernet.split(/\s+/)
                var jdx = 0
                tmp.map(function(tok,idx,me){
                    if(tok == "="){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,arhs,jdx)){
                        vkeys.push(idx)
                        if(++jdx==arhs.length){
                            self._subnetFOUND = true
                            vkeys.map(function(kdx,ii){
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                Proof[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = alhs.map(function(atok){ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    Proof[kdx] = alhs.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                // FAIL? Attempt lemma substitution //
                if(self._subnetFOUND == false){
                    postMessage({ source:'rewrite',_subnet:self._subnet,_supernet:self._supernet,_id:self._id,val:Proof.join(" "),indir:u.indir },g_origin)
                } else if(self._subnetFOUND){
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        var solutionComplete = Proof.solutionComplete("Expand")
                        self._history[val] = true
                        g_history[val] = true // comment-out to view other partial-solutions //
                        if(self._stack.length){
                            self._solutionEditor.appendlog(self._stack.join('<br>'))
                            self._stack=[]
                        }
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        if(solutionComplete){
                            self._solutionEditor.appendlog(Proof.join(" ")+solutionComplete)
                        } else {
                            postMessage({ source:self._guid,val:Proof.join(" "),indir:u.indir },g_origin)
                        }
                        console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/<br><br>/,"")}`)
                    }
                }
            }
        }
    }
    self._lemmaGovernor = function(e){
        var u = e.data
        if(u.source.startsWith("rewrite") && self._guid.startsWith("lemma") && self._id != u._id && self._subnet && self._supernet){
            var val = u.val
            self._subnetFOUND = false
            if(self._isOnline && !(val in g_history) && !(val in self._history) ){
                var id = u._id
                var stream = val.split(/\s+/)
                var from = (u.indir=='Expand') ? self._supernet.split(/\s+/) : self._subnet.split(/\s+/) ;
                var to = (u.indir=='Expand') ? self._subnet.split(/\s+/) : self._supernet.split(/\s+/) ;
                var statement = (u._subnet+' = '+u._supernet).split(/\s+/)
                var nextStatement = (u._subnet+' = '+u._supernet).split(/\s+/)
                var tmp = [];
                var buff = [];
                var intranet = [];
                var vkeys = [];
                // iff SUCCESS //
                var tmpHTML = {
                    pre:[...statement],
                    post:[...statement],
                }
                var j=0
                // rewrite the axiom //
                statement && statement.map((v,i,me)=>{
                    if(v==from[j]) {
                        vkeys.push(i)
                        if(++j==from.length){
                            vkeys.map((idx,k,too)=>{
                                tmpHTML.pre[idx] = me[idx]+self._id.addTAG('sub')
                                tmpHTML.post[idx] = null
                                nextStatement[idx] = null
                                if(k==0){ /* left-associative expressions are DECIDABLE */
                                    nextStatement[idx] = to.join(' ')
                                    tmpHTML.post[idx] = to.map((w,kk,three)=>{
                                        w+=self._id.addTAG('sub')
                                        return w
                                    }).join(' ');
                                }
                            })
                            var statusCODE = nextStatement.join(' ').stripWhiteSpace()
                            if(statusCODE in g_history){
                                return
                            } else {
                                g_history[statusCODE] = true
                                !self._subnetFOUND && (self._subnetFOUND=true);
                            }
                            j=0
                            vkeys = []
                        }
                    }
                    return v
                })
                // try a novel proofstep with the axiom //
                if(self._subnetFOUND && !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                    var tmp000 = nextStatement.join(' ').stripWhiteSpace().split(/\s+=\s+/)
                    var rhs = (tmp000.length>1) ? "" : u._supernet;
                    //self._solutionEditor.appendlog(tmpHTML.pre.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                    //self._solutionEditor.appendlog(tmpHTML.post.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                    self._stack.push(
                        tmpHTML.pre.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>', 
                        tmpHTML.post.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                    var w = []
                    if(tmp000.length>1){
                        w = (tmp000[0].length>tmp000[1].length) ? [tmp000[0],tmp000[1]] : [tmp000[1],tmp000[0]] ;
                    } else {
                        w = (tmp000[0].length>u._supernet.length) ? [tmp000[0],u._supernet] : [u._supernet,tmp000[0]] ;
                    }
                    var guid = g_code.push(new _AXIOM_
                        ({
                            _guid:"lemma_"+g_GUID++,
                            _id:id,
                            _subnet:w[0],
                            _supernet:w[1],
                            _bidirectional:self._bidirectional,
                            _stack:[...self._stack],
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