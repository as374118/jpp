all: test.vl
	ghc --make Interpreter.hs -o interpreter
grammar: varlang.cf
	happy -gca ParVarlang.y
	alex -g LexVarlang.x
	bnfc -haskell varlang.cf
