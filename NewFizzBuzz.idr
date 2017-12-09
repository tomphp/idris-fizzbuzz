data DividesBy : (n : Nat) -> (d : Nat) -> Type where
  Zero : (d : Nat) -> DividesBy 0 d
  MultipleOf : (DividesBy n d) -> DividesBy (n + d) d

mkDividesBy : (multiplier : Nat) -> (divisor : Nat) -> DividesBy (multiplier * divisor) divisor
mkDividesBy Z divisor = Zero divisor
mkDividesBy (S newMultiplier) divisor = rewrite plusCommutative divisor (newMultiplier * divisor) in
                                               MultipleOf (mkDividesBy newMultiplier divisor)

convertType : (value : DividesBy (multiplier * divisor) divisor) -> (n : Nat) -> (multiplier * divisor = n) -> DividesBy n divisor
convertType value (multiplier * divisor) Refl = value

isDivisibleByNZ : (n : Nat) -> (d : Nat) -> (nz : Not (d = 0)) -> Maybe (DividesBy n d)
isDivisibleByNZ n Z nz = void (nz Refl)
isDivisibleByNZ n d nz = let multiplier = divNatNZ n d nz in
                             (case decEq (multiplier * d) n of
                                   (Yes prf) => Just (convertType (mkDividesBy multiplier d) n prf)
                                   (No contra) => Nothing)

isDivisibleBy : (n : Nat) -> (d : Nat) -> Maybe (DividesBy n d)
isDivisibleBy n d = case decEq d Z of
                         (Yes prf) => Nothing
                         (No contra) => isDivisibleByNZ n d contra

data Fizzy : (k : Nat) -> Type where
  TheFizz : (k : Nat) -> (prf : 3 = k) -> Fizzy k

data Buzzy : (k : Nat) -> Type where
  TheBuzz : (k : Nat) -> (prf : 5 = k) -> Buzzy k

data FizzBuzzy : Nat -> Type where
  TheFizzBuzz : (k : Nat) -> (15 = k) -> FizzBuzzy k

data FizzBuzzT : (k : Nat) -> Type where
  Fizz : (Fizzy k) -> FizzBuzzT k
  Buzz : (Buzzy k) -> FizzBuzzT k
  FizzBuzz : (FizzBuzzy k) -> FizzBuzzT k
  Number : (k : Nat) -> FizzBuzzT k

fizzNotPossible : (contra : (3 = k) -> Void) -> Fizzy k -> Void
fizzNotPossible contra (TheFizz k prf) = contra prf

isFizz : (k : Nat) -> Dec (Fizzy k)
isFizz k = case decEq 3 k of
                (Yes prf) => Yes (TheFizz k prf)
                (No contra) => No (fizzNotPossible contra) 


buzzNotPossible : (contra : (5 = k) -> Void) -> Buzzy k -> Void
buzzNotPossible contra (TheBuzz k prf) = contra prf

isBuzz : (k : Nat) -> Dec (Buzzy k)
isBuzz k = case decEq 5 k of
                (Yes prf) => Yes (TheBuzz k prf)
                (No contra) => No (buzzNotPossible contra)

fizzBuzzNotPossible : (contra : (fromInteger 15 = k) -> Void) -> FizzBuzzy k -> Void
fizzBuzzNotPossible contra (TheFizzBuzz k prf) = contra prf

isFizzBuzz : (k : Nat) -> Dec (FizzBuzzy k)
isFizzBuzz k = case decEq 15 k of
                    (Yes prf) => Yes (TheFizzBuzz k prf)
                    (No contra) => No (fizzBuzzNotPossible contra)

doFizzBuzz : (k : Nat) -> FizzBuzzT k
doFizzBuzz k
  = case isFizz k of
         (Yes prf) => Fizz prf
         (No contra) => case isBuzz k of
                             (Yes prf) => Buzz prf
                             (No contra) => (case isFizzBuzz k of
                                                  (Yes prf) => FizzBuzz prf
                                                  (No contra) => Number k)

fizzBuzz : Nat -> String
fizzBuzz k = case doFizzBuzz k of
                  (Fizz x) => "fizz"
                  (Buzz x) => "buzz"
                  (FizzBuzz x) => "fizzbuzz"
                  (Number k) => show k
