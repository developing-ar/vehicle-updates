-- Correctness conditions for the Boolean AND gate

truthy : Rat -> Bool
truthy x = x >= 0.5

correctOutput : Bool
correctOutput = truthy 0
