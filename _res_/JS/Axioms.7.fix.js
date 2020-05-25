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
      +Lemmas (Enabled)
      +Scoping functionality

  STYLEGUIDE:
    http://google-styleguide.googlecode.com/svn/trunk/javascriptguide.xml

  REFERENCE:
      Substitution methods:
      1. (direct) AXIOMATIC: 1 + 1 = 2
      2. (indirect) LEMMA SUBSTITUTION: 1 <== 1/1

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
    self._auto = function(e){
    }
    self._balance = function(e){
    }
    self._reduce_stepwise = function(){
    }
    self._expand_stepwise = function(){
    }
    self._reduce = function(e){
        var u = e.data
        if(
            u.source.startsWith('axiom') &&
            self._guid.startsWith('axiom') &&
            self._isOnline &&
            self._lhs &&
            self._rhs &&
            (u.source != self._guid) &&
            u.indir.match(/Reduce|Auto/)  &&
           !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            var ProofFailed = false
            u._stack = (u._stack && u._stack.length) ? u._stack : [] ;
            if(
                !(val in g_history) &&
                !(val in self._history)
            ){
                u._lhs || (u._lhs=val.split(/\s+=\s+/)[0])
                u._rhs || (u._rhs=val.split(/\s+=\s+/)[1])
                var from = self._lhs.split(/\s+/) ;
                var to = self._rhs.split(/\s+/) ;
                var statement
                var nextStatement
                var COMPOUND = ((self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)) && true)
                if(COMPOUND){
                    statement = (u._lhs+' = '+u._rhs).split(/\s+/)
                    nextStatement = (u._lhs+' = '+u._rhs).split(/\s+/)
                } else /* SIMPLE */ {
                    statement = u._lhs.split(/\s+/)
                    nextStatement = u._lhs.split(/\s+/)
                }
                var vkeys = []
                var tmpHTML = {
                    pre:[...u.Proof],
                    post:[...u.Proof] }
                var jdx = 0
                statement && statement.map(function(tok,idx,me){
                    if(tok == "="){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,from,jdx)){
                        vkeys.push(idx)
                        if(++jdx==from.length){
                            g_code._passRound()
                            self._subnetFOUND = true
                            vkeys.map(function(kdx,ii){
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                nextStatement[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map(function(atok){ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    nextStatement[kdx] = to.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                if(
                    self._subnetFOUND
                ){
                    var P = nextStatement.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete("Reduce")
                    self._history[val] = true
                    g_history[val] = true // comment-out to view other partial-solutions //
                    var rhs = (P.findIndex((n)=>{ return n=='=' }) > -1) ? "" : ` = ${u._rhs}` ;
                    if(solutionComplete){
                        if(u._stack.length){
                            self._solutionEditor.appendlog(u._stack.join('<br><br>'))
                            u._stack = []
                        }
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        self._solutionEditor.appendlog(P.join(" ")+rhs+solutionComplete)
                    } else {
                        u._stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        Proof=P;
                        (u.indir=='Auto') && postMessage({
                            source:self._guid,
                            _id:self._id,
                            _lhs:self._lhs,
                            _rhs:self._rhs,
                            Proof:Proof,
                            indir:'Expand',
                            _stack:u._stack
                            },g_origin);
                        postMessage({
                            source:self._guid,
                            _id:self._id,
                            _lhs:self._lhs,
                            _rhs:self._rhs,
                            Proof:Proof,
                            indir:'Reduce',
                            _stack:u._stack
                            },g_origin)
                    }
                    console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/(<br>)+/,"")}`)
                }
                /* NEXT PROOFSTEP */
                /*
                postMessage({
                    source:(self._subnetFOUND) ? self._guid : 'rewrite',
                    _id:self._id,
                    _lhs:self._lhs,
                    _rhs:self._rhs,
                    Proof:Proof,
                    indir:u.indir,
                    _stack:u._stack
                    },g_origin)
                */
            } else {
                clearTimeout(g_code.activeThread)
                g_code.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        if(u._stack.length){
                            self._solutionEditor.appendlog(u._stack.join('<br><br>'))
                            u._stack = []
                        }
                        if(u.indir=='Auto'){
                            g_code._resetRound()
                            self._solutionEditor.appendlog("<br>========( Reduce )=========<br>========( Expand )=========<br>")
                            reset("partial")
                            console.log("Prove via Reduce failed; now attempting Expand...")
                            postMessage({
                                source:"axiomROOT",
                                Proof:g_code.Theorem.lemma,
                                indir:"Expand"
                                },g_origin)
                        }
                    }
                },0)
            }
        }
    }
    self._expand = function(e){
        var u = e.data
        if(
            u.source.startsWith('axiom') &&
            self._guid.startsWith('axiom') &&
            self._isOnline &&
            self._lhs &&
            self._rhs &&
            (u.source != self._guid) &&
            u.indir.match(/Expand/) &&
           !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)
        ){
            var val = u.Proof.join(' ')
            self._subnetFOUND = false
            u._stack = (u._stack && u._stack.length) ? u._stack : [] ;
            if(
                !(val in g_history) &&
                !(val in self._history)
            ){
                u._lhs || (u._lhs=val.split(/\s+=\s+/)[0])
                u._rhs || (u._rhs=val.split(/\s+=\s+/)[1])
                var from = self._rhs.split(/\s+/)//(u.indir=='Expand') ? self._rhs.split(/\s+/) : self._lhs.split(/\s+/) ;
                var to = self._lhs.split(/\s+/)//(u.indir=='Expand') ? self._lhs.split(/\s+/) : self._rhs.split(/\s+/) ;
                var statement
                var nextStatement
                var COMPOUND = ((self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)) && true)
                if(COMPOUND){
                    statement = (u._lhs+' = '+u._rhs).split(/\s+/)
                    nextStatement = (u._lhs+' = '+u._rhs).split(/\s+/)
                } else /* SIMPLE */ {
                    statement = u._rhs.split(/\s+/)
                    nextStatement = u._rhs.split(/\s+/)
                }
                var vkeys = []
                var tmpHTML = {
                    pre:[...u.Proof],
                    post:[...u.Proof]
                }
                var jdx = 0
                statement && statement.map(function(tok,idx,me){
                    if(tok == "="){
                        jdx=0
                    }
                    if(self._scope_satisfied(tok,me,idx,from,jdx)){
                        vkeys.push(idx)
                        if(++jdx==from.length){
                            self._subnetFOUND = true
                            vkeys.map(function(kdx,ii){
                                tmpHTML.pre[kdx] += self._id.addTAG("sub")
                                tmpHTML.post[kdx] = null
                                nextStatement[kdx] = null
                                if(ii==0){
                                    tmpHTML.post[kdx] = to.map(function(atok){ return (atok + self._id.addTAG("sub")) }).join(" ")
                                    nextStatement[kdx] = to.join(" ")
                                }
                            })
                            jdx=0
                            vkeys = []
                        }
                    }
                    return tok
                });
                if(
                    self._subnetFOUND
                ){
                    var P = nextStatement.collapseEmptyCells()
                    var solutionComplete = P.solutionComplete("Expand")
                    self._history[val] = true
                    g_history[val] = true // comment-out to view other partial-solutions //
                    var lhs = (P.findIndex((n)=>{ return n=='=' }) > -1) ? "" : `${u._lhs} = ` ;
                    if(solutionComplete){
                        if(u._stack.length){
                            self._solutionEditor.appendlog(u._stack.join('<br><br>'))
                            u._stack=[]
                        }
                        self._solutionEditor.appendlog(tmpHTML.pre.join(" "))
                        self._solutionEditor.appendlog(tmpHTML.post.join(" "))
                        self._solutionEditor.appendlog(lhs + P.join(" ")+solutionComplete)
                    } else {
                        u._stack.push(
                            tmpHTML.pre.join(" "),
                            tmpHTML.post.join(" "))
                        Proof=P;
                        postMessage({
                            source:self._guid,
                            _id:self._id,
                            _lhs:self._lhs,
                            _rhs:self._rhs,
                            Proof:Proof,
                            indir:'Expand',
                            _stack:u._stack
                            },g_origin);
                        (u.indir=='Auto') && postMessage({
                            source:self._guid,
                            _id:self._id,
                            _lhs:self._lhs,
                            _rhs:self._rhs,
                            Proof:Proof,
                            indir:'Reduce',
                            _stack:u._stack
                            },g_origin)
                    }
                    console.log("Source:",u.source,"; target:",`${self._guid} (Partial Solution Found) ${solutionComplete.replace(/(<br>)+/,"")}`)
                }
                /* NEXT PROOFSTEP */
                /*
                postMessage({
                    source:(self._subnetFOUND) ? self._guid : 'rewrite',
                    _id:self._id,
                    _lhs:self._lhs,
                    _rhs:self._rhs,
                    Proof:Proof,
                    indir:u.indir,
                    _stack:u._stack
                    },g_origin)
                */
            } else {
                clearTimeout(g_code.activeThread)
                g_code.activeThread=setTimeout(()=>{
                    if(!self._solutionEditor.innerText.match(/\nQ\.E\.D\./)){
                        if(u._stack.length){
                            self._solutionEditor.appendlog(u._stack.join('<br><br>'))
                            u._stack = []
                        }
                        g_code._resetRound()
                        reset("partial")
                        console.log("Prove via Expand failed - EXIT 0")
                    }
                },0)
            }
        }
    }
    self._lemmaGovernor = function(e){
        var u = e.data
        if(
            u.source.startsWith('rewrite') &&
            self._guid.startsWith('lemma') &&
            self._isOnline &&
            self._id != u._id &&
            self._lhs &&
            self._rhs &&
           !self._solutionEditor.innerText.match(/\nQ\.E\.D\./)
        ){
            var ii=(u._id+'p'+self._id)
            if(ii in self._history)
                return
            self._history[ii] = true
            self._subnetFOUND = false
            u._stack = (u._stack && u._stack.length) ? u._stack : [] ;
            var id = u._id
            var from = (u.indir=='Expand') ? self._rhs.split(/\s+/) : self._lhs.split(/\s+/) ;
            var to = (u.indir=='Expand') ? self._lhs.split(/\s+/) : self._rhs.split(/\s+/) ;
            var statement
            var nextStatement
            var COMPOUND = ((self._lhs.match(/\s+=\s+/) || self._rhs.match(/\s+=\s+/)) && true)
            if(COMPOUND){
                if(u.indir=='Expand'){
                    statement = (u._lhs+' = '+u._rhs).split(/\s+/)
                    nextStatement = (u._lhs+' = '+u._rhs).split(/\s+/)
                } else /* Auto|Reduce */ {
                    statement = (u._rhs+' = '+u._lhs).split(/\s+/)
                    nextStatement = (u._rhs+' = '+u._lhs).split(/\s+/)
                }
            } else /* SIMPLE */ {
                if(u.indir=='Expand'){
                    statement = u._rhs.split(/\s+/)
                    nextStatement = u._lhs.split(/\s+/)
                } else /* Auto|Reduce */ {
                    statement = u._lhs.split(/\s+/)
                    nextStatement = u._rhs.split(/\s+/)
                }
            }
            var vkeys = [];
            // iff SUCCESS //
            var tmpHTML = {
                pre:[...statement],
                post:[...statement],
            }
            var j=0
            var statusCODE;
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
                                    w+=(ii).addTAG('sub')
                                    return w
                                }).join(' ');
                            }
                        })
                        statusCODE = nextStatement.collapseEmptyCells().join(' ')
                        !self._subnetFOUND && (self._subnetFOUND=true);
                        j=0
                        vkeys = []
                    }
                }
                return v
            })
            if(
                self._subnetFOUND
            ){
                var tmp000 = statusCODE.split(/\s+=\s+/)
                var rhs = (tmp000.length>1) ? "" : u._rhs;
                self._stack.push(
                    tmpHTML.pre.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>',
                    tmpHTML.post.join(" ")+rhs+' <prooflink>*** Lemma ***</prooflink>')
                var w = []
                if(tmp000.length>1){
                    w = (tmp000[0].length>tmp000[1].length) ? [tmp000[0],tmp000[1]] : [tmp000[1],tmp000[0]] ;
                } else {
                    w = (tmp000[0].length>u._rhs.length) ? [tmp000[0],u._rhs] : [u._rhs,tmp000[0]] ;
                }
                g_code.push(new _AXIOM_
                    ({
                        _guid:'axiom_'+ii,
                        _id:g_GUID,
                        _lhs:w[0],
                        _rhs:w[1],
                        _bidirectional:false,
                        _stack:[...self._stack],
                        _history:{},
                        _isOnline:true,
                        _false:"68934A3E9455FA72420237EB05902327",
                        _basenetFOUND:"68934A3E9455FA72420237EB05902327",
                        _solutionEditor:g_code.solutionEditor
                    })
                );
                var obj=g_code[g_GUID]
                // try a new proofstep using the axiom //
                postMessage({
                    source:"axiomROOT",
                    Proof:g_code.Theorem.lemma,
                    _stack:obj._stack,
                    indir:u.indir
                    },g_origin)
                g_GUID++
            }
            // test: axiom <==> basenet //
            if(self._bidirectional) {

            }
        }
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
  //addEventListener("message",self._lemmaGovernor)
}