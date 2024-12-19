@network
f : Tensor Rat [1,1] -> Tensor Rat [1,1]

zeroD : Tensor Rat []
zeroD = 2.5

oneD : Tensor Rat [1]
oneD = [1]

twoD : Tensor Rat [1, 1]
twoD = [oneD]

lookup2D : Rat
lookup2D = twoD ! 0 ! 0

addition : Tensor Rat [1, 1]
addition = twoD + twoD

subtraction : Tensor Rat [1, 1]
subtraction = twoD - twoD

@property
p : Bool
p = forall i j . (f subtraction + addition) ! i ! j >= 0
