-- Correctness conditions for the Boolean AND gate

correctOutput : Rat -> Bool
correctOutput x1 = x1 >= 0.5

@property
andGateCorrect : Bool
andGateCorrect = forall x1 . correctOutput x1
