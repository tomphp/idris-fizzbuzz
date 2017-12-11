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

IsFizz : Nat -> Type
IsFizz k = k `IsDivisibleBy` 3

IsBuzz : Nat -> Type
IsBuzz k = k `IsDivisibleBy` 5

data FizzBuzzT : (k : Nat) -> Type where
  Fizz : (k : Nat) -> IsFizz k -> Not (IsBuzz k) -> FizzBuzzT k
  Buzz : (k : Nat) -> Not (IsFizz k) -> IsBuzz k -> FizzBuzzT k
  FizzBuzz : (k : Nat) -> IsFizz k -> IsBuzz k -> FizzBuzzT k
  Number : (k : Nat) -> Not (IsFizz k) -> Not (IsBuzz k) -> FizzBuzzT k

fizzBuzz : (k : Nat) -> FizzBuzzT k
fizzBuzz k
  = case k `isDivisibleBy` 3 of
         Yes isFizz
           => case k `isDivisibleBy` 5 of
                   Yes isBuzz => FizzBuzz k isFizz isBuzz
                   No isNotBuzz => Fizz k isFizz isNotBuzz
         No isNotFizz
           => case k `isDivisibleBy` 5 of
                   Yes isBuzz => Buzz k isNotFizz isBuzz
                   No isNotBuzz => Number k isNotFizz isNotBuzz

showFizzBuzz : Nat -> String
showFizzBuzz k = case fizzBuzz k of
                  (Fizz k _ _) => "fizz"
                  (Buzz k _ _) => "buzz"
                  (FizzBuzz k _ _) => "fizzbuzz"
                  (Number k _ _) => show k
