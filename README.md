NOTES

    Compatibility: Chrome 53+ (Windows) | Firefox 123.0.1+ (Windows)

STYLEGUIDE

    GOOD FORMATTING

        TEST CASE [PASS]
        { 1 } { + } { 1 } = { 2 }
        { 2 } { + } { 2 } = { 4 }
        { 4 } { + } { 2 } = { 6 }
        { 1 } { + } { 1 } { + } { 1 } { + } { 1 } { + } { 1 } { + } { 1 } = { 2 }
        Prove { 1 } { + } { 2 } { + } { 2 } { + } { 1 } = { 6 }

        TEST CASE [PASS]
        ( { a } + { b } ) ^ { 2 } = { { c } ^ { 2 } } + { 2ab }
        { { a } ^ { 2 } } + { 2ab } + { b ^ { 2 } } = ( { a } + { b } ) ^ { 2 }
        ( { a } + { b } ) ^ { 2 } - { 2ab } = { c } ^ { 2 }
        { { a } ^ { 2 } } + { 2ab } + { b ^ { 2 } } - { 2ab } = { { a } ^ { 2 } } + { { b } ^ { 2 } }
        Prove { { a } ^ { 2 } } + { { b } ^ { 2 } } = { c } ^ { 2 }

        TEST CASE [PASS]
        { { a } raised { 2 } } plus { 2ab } plus { b raised { 2 } } <== ( { a } plus { b } ) raised { 2 }
        ( { a } plus { b } ) raised { 2 } minus { 2ab } = { c } raised { 2 } <== ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
        { { a } raised { 2 } } plus { 2ab } minus { 2ab } plus { b raised { 2 } } ==> { { a } raised { 2 } } plus { { b } raised { 2 } }
        ( { a } plus { b } ) raised { 2 } = { { c } raised { 2 } } plus { 2ab }
        Prove { { a } raised { 2 } } plus { { b } raised { 2 } } = { c } raised { 2 }

        TEST CASE [PASS]
        primes = { a } raised { 2 } + { b } raised { 2 } , where (a,b) in setz
        { 1 } mod { 4 } = { a } raised { 2 } + { b } raised { 2 }
        Prove primes = { 1 } mod { 4 }

    POOR FORMATTING

        TEST CASE: RENDER [PASS], PROOF [FAIL]
        {{a}raised{2}}plus{2ab}plus{b raised{2}}<==({a}plus{b})raised{2}
        ({a}plus{b})raised{2}minus{2ab}={c}raised{2}<==({a}plus{b})raised{2}={{c}raised{2}}plus{2ab}
        {{a}raised{2}}plus{2ab}minus{2ab}plus{b raised{2}}==>{{a}raised{2}}plus{{b}raised{2}}
        ({a}plus{b})raised{2}={{c}raised{2}}plus{2ab}
        Prove {{a}raised{2}}plus{{b}raised{2}}={c}raised{2}

    SYMBOL LIBRARY

        ref: https://documentation.libreoffice.org

PROOFGUIDE

    LEMMA SUBSTITUTION FORMAT

        { LHS... } (<==|<==>|==>) { RHS... } [, comment]
        .
        .

    AXIOM FORMAT

        { LHS... } = { RHS... } [, comment]
        .
        .

    PROOF FORMAT
        Prove { LHS... } = { RHS... }

    QUICK FORMAT

        TEST CASE [PASS]
        primes = a raised 2 + b raised 2 , where (a,b) in setz
        1 mod 4 = a raised 2 + b raised 2
        Prove primes = 1 mod 4

    SCOPED FORMAT

        TEST CASE [PASS]
        primes = { a } raised { 2 } + { b } raised { 2 } , where (a,b) in setz
        { 1 } mod { 4 } = { a } raised { 2 } + { b } raised { 2 }
        Prove primes = { 1 } mod { 4 }

## Screenshot 1  
![screenshot](IMG/Screenshot_2018-06-03_12-17-39.png)  
  
## Screenshot 2  
![screenshot](IMG/sample_screenshot.png)  
  
## Screenshot 3  
![screenshot](IMG/sample_screenshot_3.png)
  
## Screenshot 4  
![screenshot](IMG/sample_screenshot_5.png) 
