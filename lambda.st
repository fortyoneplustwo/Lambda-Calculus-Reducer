Object subclass: LambdaExp [
    isVariable [ ^false ]
    isAbstraction [ ^false ]
    isApplication [ ^false ]

    ifVariable: varBlock ifAbstraction: absBlock ifApplication: appBlock [
        self isVariable ifTrue: [
            ^varBlock value
        ].
        self isAbstraction ifTrue: [
            ^absBlock value
        ].
        self isApplication ifTrue: [
            ^appBlock value
        ].
        self error: 'Invalid type'
    ]

    reduceWith: block steps: ssteps [
        | exp steps next |
        exp := self.
        steps := ssteps.
        [ steps > 0 ] whileTrue: [
            next := block value: exp.
            next isNil ifTrue: [ ^exp ].
            exp := next.
            steps := steps - 1.
        ].
        ^exp
    ]

    freeVars [
        ^self freeVars: (Dictionary new)
    ]

    printString [
        ^self displayString
    ]
]

LambdaExp subclass: LambdaVar [
    | name |

    LambdaVar class >> withName: name [
        | r |
        r := super new.
        r init: name.
        ^r
    ]

    init: sname [
        name := sname.
    ]

    dup [
        ^LambdaVar withName: name
    ]

    isVariable [ ^true ]

    name [
        ^name
    ]

    freeVars: map [
        map at: name put: self.
        ^map
    ]

    displayString [
        ^(name asString)
    ]

    "**********************"
    toDeBruijn: varlist [
    	| i |
    	i := varlist size.
    	[ i > 0 ] whileTrue: [
    		((varlist at: i) = name) ifTrue: [
    			name := ((varlist size) + 1 - i).
    			i := 0.
    		] ifFalse: [
    			i := i - 1.
    		].
    	].
    ]

    alpha: oldname for: newname [
    	oldname = name ifTrue: [ name := newname ]
    ]
    "************************"
]

LambdaExp subclass: LambdaAbs [
    | var body |

    LambdaAbs class >> withVar: var body: body [
        | r |
        r := super new.
        r init: var body: body.
        ^r
    ]

    init: svar body: sbody [
        var := svar.
        body := sbody.
    ]

    dup [
        ^LambdaAbs withVar: var body: body dup
    ]

    isAbstraction [ ^true ]

    var [
        ^var
    ]

    body [
        ^body
    ]

    freeVars: map [
        | hadKey |
        hadKey := map includesKey: var.
        body freeVars: map.
        hadKey ifFalse: [ map removeKey: var ifAbsent: [nil]. ].
        ^map
    ]

    displayString [
        ^'(\' , var , '.' , body displayString , ')'
    ]

    "********************"
    toDeBruijn: varlist [
    	varlist add: var.
    	var := ''.
    ]

    alphaStep: oldname for: newname [
    	| map |
    	body ifVariable: [
    		(body name = oldname) ifTrue: [ 
    			body alpha: oldname for: newname.
    		].
    	] ifAbstraction: [
    		map := body freeVars.
    		map := body freeVars: map.
    		(map includesKey: oldname) ifTrue: [
    			body alphaStep: oldname for: newname.
    		].
    	] ifApplication: [
    		body alpha: oldname for: newname.
    	].
    ]

    alpha: oldname for: newname [
    	var = oldname ifTrue: [
    		self alphaStep: oldname for: newname.
    		var := newname.
    	].
    ]

    substitute: param with: arg [
    	body isVariable ifTrue: [
    		body = param ifTrue: [ 
    			body := arg.
    		].
    	] ifFalse: [
    		body substitute: param with: arg.
    	].
    	^self.
    ]

    bodyReplaceWith: newbody [ body := newbody ]
    "*******************"
]

LambdaExp subclass: LambdaApp [
    | rator rand |

    LambdaApp class >> withRator: rator rand: rand [
        | r |
        r := super new.
        r init: rator rand: rand.
        ^r
    ]

    init: srator rand: srand [
        rator := srator.
        rand := srand.
    ]

    dup [
        ^LambdaApp withRator: rator dup rand: rand dup
    ]

    isApplication [ ^true ]

    rator [
        ^rator
    ]

    rand [
        ^rand
    ]

    freeVars: map [
        rator freeVars: map.
        rand freeVars: map.
        ^map
    ]

    displayString [
        ^'(' , rator displayString , ' ' , rand displayString , ')'
    ]

    "*************************"
    ratorReplaceWith: r [
		rator := r.
		^self.
	]

	randReplaceWith: r [
		rand := r.
		^self.
	]


	alpha: oldname for: newname [
		rator alpha: oldname for: newname.
		rand alpha: oldname for: newname.
	]

	substitute: param with: arg [
		rator isVariable ifTrue: [ 
			rator name = param ifTrue: [ rator := arg ].
		] ifFalse: [
			rator substitute: param with: arg.	
		].
		rand isVariable ifTrue: [ 
			rand name = param ifTrue: [ rand := arg ].
		] ifFalse: [
			rand substitute: param with: arg.	
		].
	]
	"*************************"
]

Object subclass: LambdaParser [
    | text index tok |

    LambdaParser class >> new [
        self error: 'Use new: text'.
    ]

    LambdaParser class >> new: text [
        | r |
        r := super new.
        r init: text.
        ^r
    ]

    LambdaParser class >> parse: text [
        | p |
        p := self new: text.
        ^p parse
    ]

    init: stext [
        text := stext.
        index := 1.
        tok := ''.
    ]

    token [
        | i |
        index := index + (tok size).
        i := index.

        i > text size ifTrue: [
            " Out of bounds "
            tok := nil.
            ^tok
        ].

        (text at: i) isSeparator ifTrue: [
            " Skip it "
            tok := ' '.
            ^self token
        ].

        (text at: i) isAlphaNumeric ifTrue: [
            " Tokenize the whole name or number "
            [(text at: i ifAbsent: [$$]) isAlphaNumeric] whileTrue: [
                i := i + 1.
            ].
            tok := text copyFrom: index to: (i-1).

        ] ifFalse: [
            " All other tokens are of length 1 "
            tok := text copyFrom: i to: i.

        ].

        ^tok
    ]

    parse [
        | r |
        r := self parseApplication.
        r isNil ifTrue: [ self error: 'Failed to parse application' ].
        tok isNil ifFalse: [ self error: 'Unterminated expression' ].
        ^r
    ]

    parseApplication [
        | cur next |
        cur := nil.

        " The top-level parser is for applications "
        [ self token isNil ] whileFalse: [
            next := self parseNonApplication.
            next isNil ifTrue: [
                ^cur
            ].
            cur isNil ifTrue: [
                cur := next.
            ] ifFalse: [
                cur := LambdaApp withRator: cur rand: next.
            ].
        ].

        ^cur
    ]

    parseNonApplication [
        tok = '(' ifTrue: [ ^self parseParenthetical ].
        tok = '\' ifTrue: [ ^self parseAbstraction ].
        (tok at: 1) isAlphaNumeric ifTrue: [ ^self parseVariable ].
        ^nil
    ]

    parseParenthetical [
        | r |
        r := self parseApplication.
        (tok = ')') ifFalse: [
            self error: 'Unterminated parenthetical.'
        ].
        ^r
    ]

    parseAbstraction [
        | var body |

        " We allow a variable form or a variable-less (deBruijn) form, but var
          must be set "
        self token.
        (tok at: 1) isAlphaNumeric ifTrue: [
            var := tok.
            self token.
        ] ifFalse: [
            var := ''.
        ].

        tok = '.' ifFalse: [
            self error: 'Expected .'
        ].

        body := self parseApplication.

        " tok is currently the *next* token, but it should be the last token we
          actually consumed, so stub it "
        tok := ''.

        ^LambdaAbs withVar: var body: body
    ]

    parseVariable [
        | var |
        var := tok.
        (tok at: 1) isDigit ifTrue: [
            " A numeric (deBruijn) variable "
            var := tok asNumber.
        ].
        ^LambdaVar withName: var
    ]
]

"///////////////////////////////////"

Object subclass: Lambda [ 
	| lambdaExp |

	Lambda class >> new: exp [
		| r |
		r := super new.
		r init: exp.
		^r.
	]

	init: exp [
		lambdaExp := exp.
	]

	toDeBruijnStep: exp with: varlist [
		| definedVars |
		definedVars := (varlist deepCopy).
		exp ifVariable: [
			exp toDeBruijn: definedVars.
		] ifAbstraction: [
			exp toDeBruijn: definedVars.
			self toDeBruijnStep: (exp body) with: definedVars.
		] ifApplication: [
			self toDeBruijnStep: (exp rator) with: definedVars.
			self toDeBruijnStep: (exp rand) with: definedVars.
		].
	]

	toDeBruijn [
		self toDeBruijnStep: lambdaExp with: (OrderedCollection new).
		^lambdaExp.
	]

	aoeStep: exp [
		| A B uniqueName |
		exp ifVariable: [
			^nil
		] ifAbstraction: [
			^nil
		] ifApplication: [
		"let expression = AB"
		"if A is an abs and..."
			"if B is not reducible, substitute B in A" 
			"else if B is reducible, reduce B"
		"else if A is reducible, reduce A"
		"else if B is reducible, reduce B"
			A := (exp rator) dup.
			B := (exp rand) dup.
			(A isAbstraction) ifTrue: [
				B := (self aoeStep: (B dup)).
				(B = nil) ifTrue: [
					uniqueName := ((A var) , (self hash asString)).
					A alpha: (A var) for: uniqueName.
					A := ((A dup substitute: (A var) with: (exp rand)) body).
					^A.
				] ifFalse: [ 
					^(exp randReplaceWith: B)	
				].
			] ifFalse: [
				A := (self aoeStep: (A dup)).
				(A = nil) ifFalse: [
					^(exp ratorReplaceWith: A).
				] ifTrue: [
					B := (self aoeStep: (B dup)). 
					(B = nil) ifFalse: [ ^(exp randReplaceWith: B) ].
				].
			].
		].
	]


	aoe [ 
		lambdaExp ifNil: [ ^nil ].
		lambdaExp := (self aoeStep: (lambdaExp dup)).
		^lambdaExp.
	]

	reduceWith: block steps: ssteps [
        | exp steps next |
        steps := ssteps.
        [ steps > 0 ] whileTrue: [
        	exp := (lambdaExp dup).
            next := block value: self.
            next isNil ifTrue: [ ^exp ].
            lambdaExp := next.
            steps := steps - 1.
        ].
        ^lambdaExp.
    ]

	aoe: steps [
		lambdaExp ifNil: [ ^nil ].
		lambdaExp := (self reduceWith: [:v| v aoe] steps: steps).
		^lambdaExp.
	]

	norStep: exp [
		| rator rand uniqueName rbody |
		exp ifVariable: [
			^nil
		] ifAbstraction: [
			rbody := (self norStep: (exp body dup)).
			rbody ifNotNil: [ ^exp bodyReplaceWith: rbody ].
			^nil
		] ifApplication: [
			rator := exp rator dup.
			rand := exp rand dup.
			rator isAbstraction ifTrue: [ 
				uniqueName :=  ((rator var) , (self hash asString)).
				rator alpha: (rator var) for: uniqueName.
				rator := ((rator dup substitute: (rator var) with: (exp rand)) body).
				^rator.
			] ifFalse: [
				rator := (self norStep: (rator dup)).
				rator ifNotNil: [ ^(exp ratorReplaceWith: rator) ].
				rand := (self norStep: (rand dup)).
				rand ifNotNil: [ ^(exp randReplaceWith: rand) ].
				^nil.
			].
		].
	]

	nor [
		lambdaExp ifNil: [ ^nil ].
		lambdaExp := (self norStep: (lambdaExp dup)).
		^lambdaExp.
	]

	nor: steps [
		lambdaExp ifNil: [ ^nil ].
		lambdaExp := (self reduceWith: [:v| v nor] steps: steps).
		^lambdaExp.
	]

	etaStep: exp [
		| A B uniqueName map rbody|
		exp ifVariable:[
			^nil.
		] ifAbstraction: [
		"let expression = \x.M"
			exp body ifVariable: [
			"if body is a var, return nil"
				^nil.
			] ifAbstraction: [
			"if body is an abs, recuse on body"
				rbody := (self etaStep: (exp body)).
				rbody ifNotNil: [ ^(exp bodyReplaceWith: rbody) ].
				^nil.
			] ifApplication: [
			"if body is an application AB..."
				"if A is reducible, reduce A"
				"if B is reducible, reduce B"
				"else reduce body if B is a var and is not A var"
				A := (exp body rator) dup.
				B := (exp body rand) dup.
				A := (self etaStep: (A dup)).
				A ifNotNil: [ ^(exp replaceRatorWith: A) ].
				B := (self etaStep: (B dup)).
				B ifNotNil: [ ^(exp replaceRandWith: B) ].
				exp body rand isVariable ifTrue: [
					exp body rator isVariable ifTrue: [^nil].
					map := exp body rator freeVars.
					map := exp body rator freeVars: map.
					(map includesKey: (exp body rand)) ifTrue: [ ^nil ].
					^(exp body rator).
				] ifFalse: [ ^nil ].
			].
		] ifApplication: [
			A := (exp rator) dup.
			B := (exp rand) dup.
			A := (self etaStep: (A dup)).
			A ifNotNil: [ ^(exp replaceRatorWith: A) ].
			B := (self etaStep: (B dup)).
			B ifNotNil: [ ^(exp replaceRandWith: B) ].
			^nil.
		].
	]

	eta [
		lambdaExp ifNil: [ ^nil ].
		lambdaExp := (self etaStep: (lambdaExp dup)).
		^lambdaExp.
	]

	eta: steps [
		lambdaExp ifNil: [ ^nil ].
		lambdaExp := (self reduceWith: [:v| v eta] steps: steps).
		^lambdaExp.
	]
]
