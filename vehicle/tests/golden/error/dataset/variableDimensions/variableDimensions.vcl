@network
f : Tensor Rat [1] -> Tensor Rat [3]

s : Tensor Rat [1]
s = [1]

r : Bool
r = f [1] ! 0 > 2

test : Nat
test = if r then 2 else 3

@dataset
trainingDataset : Tensor Nat [test]
{-
(Tensor Rat) .( ((:: {Nat} ) 1) (nil {Nat} )) ~ ?9 ?11
?11 ~ ?12
?10 <= (HasVecLiterals ?9) 1
?14 <= (NatInDomainConstraint 1) ?12
-}
