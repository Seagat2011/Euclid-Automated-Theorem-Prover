Object.prototype.optimizeCallGraph=function(){
    var self = this
    const guidROOT = 'axiomROOT'
    var TheoremSUBKEY = self.Theorem.lemma.asPrimaryKey();

    let _callStack = [];

    self.map((u,i,me)=>{
        if(TheoremSUBKEY.subkeyFOUND(u._lhsSUBKEY)){
            u._lhsCallGraph[guidROOT]=true;
        }
        if(TheoremSUBKEY.subkeyFOUND(u._rhsSUBKEY)){
            u._rhsCallGraph[guidROOT]=true;
        }
        _callStack.push({
              _idx:i
            , _subnet:"_lhs"
            , _guid:u._guid
            , _subnetKey:u._lhsSUBKEY });
        _callStack.push({
              _idx:i
            , _subnet:"_rhs"
            , _guid:u._guid
            , _subnetKey:u._rhsSUBKEY });

        return u;
    });

    while(_callStack.length > 0){
    
        const u = _callStack.shift();

        const i = u._idx;
        const uGUID = u._guid;

        if(TheoremSUBKEY.subkeyFOUND(u._subnetKey)){
            if(/_lhs/.test(u._subnet)){
                self[i]._lhsCallGraph[guidROOT]=true;
            } else if(/_rhs/.test(u._subnet)){
                self[i]._rhsCallGraph[guidROOT]=true;
            }
        }

        self.map((v,j,too)=>{
            if (i != j){
                const lhsSUBNET_Flag = (u._subnetKey.subkeyFOUND(v._lhsSUBKEY) || u._subnetKey.subkeyFOUND(v._lhsSUBKEY));
                const rhsSUBNET_Flag = (u._subnetKey.subkeyFOUND(v._rhsSUBKEY) || u._subnetKey.subkeyFOUND(v._rhsSUBKEY));
                const addToLHSCallGraph_Flag = !(v._lhsCallGraph[uGUID]===true);
                const addToRHSCallGraph_Flag = !(v._rhsCallGraph[uGUID]===true);

                if (lhsSUBNET_Flag 
                    && addToLHSCallGraph_Flag){
                    v._lhsCallGraph[uGUID]=true;

                    const tmpSubnetKey = u._subnetKey.subkeyUPDATE(v._lhsSUBKEY,v._rhsSUBKEY); // (from,to) //

                    _callStack.push({
                          _idx:i
                        , _guid:u._guid
                        , _subnet:u._subnet
                        , _subnetKey:tmpSubnetKey });
                } 
                if (rhsSUBNET_Flag
                    && addToRHSCallGraph_Flag){
                    v._rhsCallGraph[uGUID]=true;

                    const tmpSubnetKey = u._subnetKey.subkeyUPDATE(v._rhsSUBKEY,v._lhsSUBKEY); // (from,to) //

                    _callStack.push({
                          _idx:i
                        , _guid:u._guid
                        , _subnet:u._subnet
                        , _subnetKey:tmpSubnetKey });
                }
            }

            return v;
        });
    }
}

Object.prototype.optimizeCallGraph=function(){
    var self = this
    const guidROOT = 'axiomROOT'
    var TheoremSUBKEY = self.Theorem.lemma.asPrimaryKey();
    let new_entry = {};

    let _callStack = [];

    self.map((u,i,me)=>{
        if(TheoremSUBKEY.subkeyFOUND(u._lhsSUBKEY)){
            u._lhsCallGraph[guidROOT]=true;
        }
        if(TheoremSUBKEY.subkeyFOUND(u._rhsSUBKEY)){
            u._rhsCallGraph[guidROOT]=true;
        }
        _callStack.push({
              _idx:i
            , _subnet:"_lhs"
            , _guid:u._guid
            , _subnetKey:u._lhsSUBKEY });
        _callStack.push({
              _idx:i
            , _subnet:"_rhs"
            , _guid:u._guid
            , _subnetKey:u._rhsSUBKEY });

        return u;
    });

    while(_callStack.length > 0){
    
        const u = _callStack.shift();

        const i = u._idx;
        const uGUID = u._guid;

        self.map((v,j,too)=>{
            if (i != j){
                const lhsSUBNET_Flag = (u._subnetKey.subkeyFOUND(v._lhsSUBKEY) || u._subnetKey.subkeyFOUND(v._lhsSUBKEY));
                const rhsSUBNET_Flag = (u._subnetKey.subkeyFOUND(v._rhsSUBKEY) || u._subnetKey.subkeyFOUND(v._rhsSUBKEY));
                const addToLHSCallGraph_Flag = !(v._lhsCallGraph[uGUID]===true);
                const addToRHSCallGraph_Flag = !(v._rhsCallGraph[uGUID]===true);

                if (lhsSUBNET_Flag 
                    && addToLHSCallGraph_Flag){
                    v._lhsCallGraph[uGUID]=true;

                    const tmpSubnetKey = u._subnetKey;

                    const isaNewEntry = !(tmpSubnetKey in new_entry);

                    if(isaNewEntry){
                        new_entry[tmpSubnetKey] = true;
                        _callStack.push({
                              _idx:i
                            , _guid:u._guid
                            , _subnet:u._subnet
                            , _subnetKey:tmpSubnetKey });
                    }
                } 
                if (rhsSUBNET_Flag
                    && addToRHSCallGraph_Flag){
                    v._rhsCallGraph[uGUID]=true;

                    const tmpSubnetKey = u._subnetKey;

                    const isaNewEntry = !(tmpSubnetKey in new_entry);

                    if(isaNewEntry){
                        new_entry[tmpSubnetKey] = true;
                        _callStack.push({
                              _idx:i
                            , _guid:u._guid
                            , _subnet:u._subnet
                            , _subnetKey:tmpSubnetKey });
                    }
                }
            }

            return v;
        });
    }
}

class AxiomTask extends Object {
    constructor({ _guid=0, _subnetKey=0, _subnet="_lhs", _hops=0 }={}){
        super();
        this._hops = _hops;
        this._guid = _guid;
        this._subnet = _subnet;
        this._subnetKey = _subnetKey;
    };
};

Object.prototype.optimizeCallGraph=function(){
    var self = this
    const guidROOT = 'axiomROOT'
    var TheoremSUBKEY = self.Theorem.lemma.asPrimaryKey();

    let _callStack = [];

    self.map((u,i,me)=>{
        if(TheoremSUBKEY.subkeyFOUND(u._lhsSUBKEY)){
            u._lhsCallGraph[guidROOT]=true;
        }
        if(TheoremSUBKEY.subkeyFOUND(u._rhsSUBKEY)){
            u._rhsCallGraph[guidROOT]=true;
        }
        _callStack.push({
              _idx:i
            , _guid:u._guid
            , _subnetKey:u._lhsSUBKEY });
        _callStack.push({
              _idx:i
            , _guid:u._guid
            , _subnetKey:u._rhsSUBKEY });

        return u;
    });

    while(_callStack.length > 0){
    
        const u = _callStack.shift();

        const i = u._idx;
        const uGUID = u._guid;

        self.map((v,j,too)=>{
            if (i != j){
                const lhsSUBNET_Flag = (u._subnetKey.subkeyFOUND(v._lhsSUBKEY) || u._subnetKey.subkeyFOUND(v._lhsSUBKEY));
                const rhsSUBNET_Flag = (u._subnetKey.subkeyFOUND(v._rhsSUBKEY) || u._subnetKey.subkeyFOUND(v._rhsSUBKEY));
                const addToLHSCallGraph_Flag = !(v._lhsCallGraph[uGUID]===true);
                const addToRHSCallGraph_Flag = !(v._rhsCallGraph[uGUID]===true);

                if (lhsSUBNET_Flag 
                    && addToLHSCallGraph_Flag){
                    v._lhsCallGraph[uGUID]=true;

                    const tmpSubnetKey = u._subnetKey.subkeyUPDATE(v._lhsSUBKEY,v._rhsSUBKEY); // (from,to) //

                    _callStack.push({
                          _idx:i
                        , _guid:u._guid
                        , _subnetKey:tmpSubnetKey });
                } 
                if (rhsSUBNET_Flag
                    && addToRHSCallGraph_Flag){
                    v._rhsCallGraph[uGUID]=true;

                    const tmpSubnetKey = u._subnetKey.subkeyUPDATE(v._rhsSUBKEY,v._lhsSUBKEY); // (from,to) //

                    _callStack.push({
                          _idx:i
                        , _guid:u._guid
                        , _subnetKey:tmpSubnetKey });
                }
            }

            return v;
        });
    }
}

    //new AxiomTask({ _guid=0, _subnetKey=0, _subnet="_lhs", _hops=0 }); //
    //let _callStack = [];
    //let _localCallStack = [];
    /*
    self.map((u,i,me)=>{
        if(TheoremSUBKEY.subkeyFOUND(u._lhsSUBKEY)){
            u._lhsCallGraph[guidROOT]=true;
        }
        if(TheoremSUBKEY.subkeyFOUND(u._rhsSUBKEY)){
            u._rhsCallGraph[guidROOT]=true;
        }
        _callStack.push({
              _guid:u._guid
            , _subnet:"_lhs"
            , _subnetKey:u._lhsSUBKEY });
        _callStack.push({
              _guid:u._guid
            , _subnet:"_rhs"
            , _subnetKey:u._rhsSUBKEY });

        return u;
    });
    */
    /*
    self.map((u,i,me)=>{
        const uGUID = u._guid;
        self.map((v,j,too)=>{
            if(i!=j){
                (u._rhsSUBKEY.subkeyFOUND(v._lhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._lhsSUBKEY)) ? (v._lhsCallGraph[uGUID]=true) : "" ;
                (u._rhsSUBKEY.subkeyFOUND(v._rhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._rhsSUBKEY)) ? (v._rhsCallGraph[uGUID]=true) : "" ;
            }
            return v
        })
        return u;
    });
    */
    
    //const N = self.length.toFactorial();

    //for(let n = 0; n < N; ++n){ // Create an all-encompassing loop; while-loops may not always converge //
    /*
    self.map((u,i,me)=>{
        const uGUID = u._guid;
        if(TheoremSUBKEY.subkeyFOUND(u._lhsSUBKEY)){
            u._lhsCallGraph[guidROOT]=true;
            / *
            if(!u._lhsCallGraph._lhsCallIDX)
                u._lhsCallGraph._lhsCallQueueRESET();
            u._lhsCallGraph._lhsCallQueueSET(
                new AxiomTask({
                      _guid:guidROOT
                    , _subnetKey:u._lhsSUBKEY
                    , _subnet:"lhs"
                    , _hops:0 }));
            _callStack.push(
                new AxiomTask({
                      _guid:guidROOT
                    , _subnetKey:u.subkeyUPDATE(TheoremSUBKEY,u._lhsSUBKEY) // (from,to) //
                    , _subnet:"lhs"
                    , _hops:0 }));
                    * /
        }
        if(TheoremSUBKEY.subkeyFOUND(u._rhsSUBKEY)){
            u._rhsCallGraph[guidROOT]=true;
            / *
            if(!u._rhsCallGraph._rhsCallIDX)
                u._rhsCallGraph._rhsCallQueueRESET();
            u._rhsCallGraph._lhsCallQueueSET(
                new AxiomTask({
                      _guid:guidROOT
                    , _subnetKey:u._rhsSUBKEY
                    , _subnet:"rhs"
                    , _hops:0 }));
            const nextSubnetKey = u.subkeyUPDATE(TheoremSUBKEY,u._rhsSUBKEY); // (from,to) //

            let _subnetKey = {};

            _subnetKey[guidROOT] = nextSubnetKey;

            _callStack.push(
                new AxiomTask({
                      _guid:guidROOT
                    , _subnetKey:nextSubnetKey
                    , _subnet:"rhs"
                    , _hops:0 }));
                    * /
        }
        * /
        self.map((v,j,too)=>{
            if(i!=j){
                (u._rhsSUBKEY.subkeyFOUND(v._lhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._lhsSUBKEY)) ? (v._lhsCallGraph[uGUID]=true) : "" ;
                (u._rhsSUBKEY.subkeyFOUND(v._rhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._rhsSUBKEY)) ? (v._rhsCallGraph[uGUID]=true) : "" ;
            }
            return v
        });
        return u
    }); // end self.map((u,i,me) //
    */

    for(let n = 0; n < N; ++n){ // Create an all-encompassing loop; while-loops may not always converge //
        if(_callStack.length > 0){
            const u = _callStack.shift();

            const i = u._idx;
            const uGUID = u._guid;

            self.map((v,j,too)=>{
                if(i!=j){
                    const lhsSUBNET_Flag = /_lhs/.test(u._subnet);
                    const rhsSUBNET_Flag = /_rhs/.test(u._subnet);
                    const axiomROOT_SUBNET_Flag = /axiomROOT/.test(u._subnet);

                    if(lhsSUBNET_Flag){

                    } else if (rhsSUBNET_Flag){

                    } else if (axiomROOT_SUBNET_Flag){

                    }
                    (u._rhsSUBKEY.subkeyFOUND(v._lhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._lhsSUBKEY)) ? (v._lhsCallGraph[uGUID]=true) : "" ;
                    (u._rhsSUBKEY.subkeyFOUND(v._rhsSUBKEY) || u._lhsSUBKEY.subkeyFOUND(v._rhsSUBKEY)) ? (v._rhsCallGraph[uGUID]=true) : "" ;
                }
                return v
            });
        } else {
            break;
        }
    }

            let axiomIDX = self[i];

            if(TheoremSUBKEY.subkeyFOUND(u._lhsSUBKEY)){
                axiomIDX._lhsCallGraph[guidROOT]=true;                
                _callStack.push({
                      _idx:i
                    , _guid:uGUID
                    , _subnetKey:u._subnetKey });
            }
            if(TheoremSUBKEY.subkeyFOUND(u._rhsSUBKEY)){
                axiomIDX._rhsCallGraph[guidROOT]=true;                
                _callStack.push({
                      _idx:i
                    , _guid:uGUID
                    , _subnetKey:u._subnetKey });
            }

            /*
            if(u._guid === axiomROOT){
                _callStack.push({
                      _idx:guidROOT
                    , _guid:guidROOT
                    , _subnet:guidROOT
                    , _subnetKey:TheoremSUBKEY });

                continue;
            }
            */

    self._reduce = function(e){
        const u = e.data;
        const StandardMode_Flag = /Reduce|Auto|Optimal/i.test(u.indir);
        if(
            u.source &&
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
           StandardMode_Flag &&
           !g_SOLVED
        ){
            var val = u.Proof.join(' ');
            if(
                !(val in self._history._reduce)
            ){
                var ProofSUBKEY = u.ProofSUBKEY;
                self._history._reduce[val]=true;
                
                let promise_0000;
                let promise_0001;

                // Likely to converge faster than the following code //
                if((u.source in self._lhsCallGraph)){
                    promise_0000 = new Promise(resolve => self._updateSubkey(u,"Reduce") );
                }
                if(u.ProofSUBKEY.subkeyFOUND(self._lhsSUBKEY)){
                    promise_0001 = new Promise(resolve => self._updateSubkey(u,"Reduce") );
                }

                Promise.all([promise_0000,promise_0001]);
            } // if(!(val in self._history._reduce)) //
        } // if(u.source && ... && !g_SOLVED) //
    }
    self._expand = async function(e){
        const u = e.data;
        const StandardMode_Flag = /Expand|Auto|Optimal/i.test(u.indir);
        if(
            u.source &&
            u.source.startsWith('axiom') &&
            self._isOnline &&
           (u.source != self._guid) &&
           StandardMode_Flag &&
           !g_SOLVED
        ){
            var val = u.Proof.join(' ');
            if(
                !(val in self._history._expand)
            ){
                var ProofSUBKEY = u.ProofSUBKEY;
                self._history._expand[val]=true;
                
                let promise_0000;
                let promise_0001;

                // Likely to converge faster than the following code //
                if((u.source in self._rhsCallGraph)){
                    promise_0000 = new Promise(resolve => self._updateSubkey(u,"Expand") );
                }
                if(u.ProofSUBKEY.subkeyFOUND(self._rhsSUBKEY)){
                    promise_0000 = new Promise(resolve => self._updateSubkey(u,"Expand") );
                }

                Promise.all([promise_0000,promise_0001]);
            } // if(!(val in self._history._expand)) //
        } // if(u.source && ... && !g_SOLVED) //
    }