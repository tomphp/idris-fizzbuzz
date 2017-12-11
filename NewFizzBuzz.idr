data IsDivisibleBy : (dividend : Nat) -> (divisor : Nat) -> Type where
  MkIsDivisibleBy : (dividend : Nat)
         -> (divisor : Nat)
         -> (prf : (modNat dividend divisor = 0))
         -> IsDivisibleBy dividend divisor

isNotAMultiple : (contra : (modNat dividend divisor = 0) -> Void) -> IsDivisibleBy dividend divisor -> Void
isNotAMultiple contra (MkIsDivisibleBy dividend divisor prf) = contra prf

isDivisibleBy : (dividend : Nat) -> (divisor : Nat) -> Dec (IsDivisibleBy dividend divisor)
isDivisibleBy dividend divisor 
  = (case decEq (modNat dividend divisor) Z of
              (Yes prf) => Yes (MkIsDivisibleBy dividend divisor prf)
              (No contra) => No (isNotAMultiple contra))

-- NotZero : Nat -> Type
-- NotZero k = Not (k = 0)

-- isZero : (k : Nat) -> Dec (k = Z)
-- isZero k = decEq k Z

data Fizzy : (k : Nat) -> Type where
  TheFizz : (k : Nat) -> (prf : k `IsDivisibleBy` 3) -> Fizzy k

data Buzzy : (k : Nat) -> Type where
  TheBuzz : (k : Nat) -> (prf : 5 = k) -> Buzzy k

data FizzBuzzy : Nat -> Type where
  TheFizzBuzz : (k : Nat) -> (15 = k) -> FizzBuzzy k

data FizzBuzzT : (k : Nat) -> Type where
  Fizz : (Fizzy k) -> FizzBuzzT k
  Buzz : (Buzzy k) -> FizzBuzzT k
  FizzBuzz : (FizzBuzzy k) -> FizzBuzzT k
  Number : (k : Nat) -> FizzBuzzT k

fizzNotPossible : (contra : (k `IsDivisibleBy` 3) -> Void) -> Fizzy k -> Void
fizzNotPossible contra (TheFizz k prf) = contra prf

isFizz : (k : Nat) -> Dec (Fizzy k)
isFizz k = case (k `isDivisibleBy` 3) of
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
