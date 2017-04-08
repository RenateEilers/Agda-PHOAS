module PHOAS2 where

import Data.String as S
open import Relation.Binary.PropositionalEquality hiding (inspect)

-------------------------------------------------------------
-- Prelude
-------------------------------------------------------------

data Nat : Set where
  Zero : Nat
  Succ : Nat -> Nat

_+_ : Nat -> Nat -> Nat
Zero + y = y
Succ x + y = Succ (x + y)

showNat : Nat -> S.String
showNat Zero = "0"
showNat (Succ n) = "S(" S.++ (showNat n) S.++ ")"

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

data _≤_ : Nat -> Nat -> Set where
  Base : ∀ {n} -> n ≤ n
  Step : ∀ {n m} -> n ≤ m -> n ≤ (Succ m)

data _<_ : Nat -> Nat -> Set where
  Base : ∀ {n} -> Zero < (Succ n)
  Step : ∀ {n m} -> n < m -> (Succ n) < (Succ m)


data Unit : Set where
  unit : Unit

data  Fin : Nat -> Set where
  FZero : ∀ {n} -> Fin (Succ n)
  FSucc : ∀ {n} -> Fin n -> Fin (Succ n)

data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

fst : {A B : Set} -> A × B -> A
fst (x , _) = x

snd : {A B : Set} -> A × B -> B
snd (_ , x) = x

≡-symm : ∀ {A : Set} {a b : A} -> a ≡ b -> b ≡ a
≡-symm refl = refl

≡-trans : ∀ {A : Set} {a b c : A} -> a ≡ b -> b ≡ c -> a ≡ c
≡-trans refl refl = refl

data Stack : Nat -> Set where
  Empty : Stack Zero
  _▻_ : {n : Nat} -> Nat -> Stack n -> Stack (Succ n)

pop : ∀ {n} -> Stack (Succ n) -> Nat
pop (x ▻ s) = x

-- Initializes a heap of a given size with Zero-values
initHeap : (n : Nat) -> Stack n
initHeap Zero = Empty
initHeap (Succ n) = Zero ▻ initHeap n

lookup : ∀ {n} -> Fin n -> Stack n -> Nat
lookup FZero (x ▻ s) = x
lookup (FSucc n) (x ▻ s) = lookup n s

update : ∀ {n} -> Fin n -> Nat -> Stack n -> Stack n
update FZero n (x ▻ s) = n ▻ s
update (FSucc f) n (x ▻ s) = x ▻ (update f n s)

fog : ∀ {n m} -> Fin n -> n ≤ m -> Fin m
fog n₁ Base = n₁
fog FZero (Step p) = FZero
fog (FSucc n₁) (Step p) = FSucc (fog n₁ (lem p))
  where lem : ∀ {n m} -> Succ n ≤ m -> n ≤ m
        lem Base = Step Base
        lem (Step p₁) = Step (lem p₁)

predFin : ∀ {n} -> Fin n -> Fin n
predFin FZero      = FZero
predFin (FSucc x)  = fog x (Step Base)

fromNat : (n : Nat) -> Fin (Succ n)
fromNat Zero      = FZero
fromNat (Succ n)  = FSucc (fromNat n)

-------------------------------------------------------------
-- Definitions for expressions
-------------------------------------------------------------

data Expr (a : Set) : Set where
  Val : Nat -> Expr a
  Add : Expr a -> Expr a -> Expr a
  Var : a -> Expr a
  Let : Expr a -> (a -> Expr a) -> Expr a

ClosedExpr : Set₁
ClosedExpr = {a : Set} -> Expr a

data _⊢_≡_  {A B : Set} : (P : A -> B -> Set) -> Expr A -> Expr B -> Set₁ where
   Val : ∀ {P} {x : Nat} -> P ⊢ (Val x) ≡ (Val x)
   Add : ∀ {P} {l₁ r₁ l₂ r₂}
         -> P ⊢ l₁ ≡ l₂ -> P ⊢ r₁ ≡ r₂
         -> P ⊢ Add l₁ r₁ ≡ Add l₂ r₂
   Var : ∀ {P x y} -> P x y -> P ⊢ Var x ≡ Var y
   Let : ∀ {P b₁ b₂ e₁ e₂} ->  P ⊢ b₁ ≡ b₂
           -> (∀ {x₁} {x₂} -> (P x₁ x₂
           ->  P ⊢ (e₁ x₁) ≡  (e₂ x₂)))
           ->  P ⊢ (Let b₁ e₁) ≡ (Let b₂ e₂)

postulate
  e≡e : ∀ {A B P} {e : ClosedExpr} -> P ⊢ e {A} ≡ e {B}

-------------------------------------------------------------
-- Basic functions over expressions
-------------------------------------------------------------

-- Evaluation
eval : Expr Nat -> Nat
eval (Val x) = x
eval (Add e₁ e₂) = eval e₁ + eval e₂
eval (Var x) = x
eval (Let e₁ e₂) = eval (e₂ (eval e₁)) 

-- Number of distinct variables in an expression
#vars : Expr Unit -> Nat
#vars (Val x) = Zero
#vars (Add e e₁) = #vars e + #vars e₁
#vars (Var x) = Zero
#vars (Let e x) = Succ Zero + (#vars e +  #vars (x unit))

-- Building a tree
tree : Nat -> ClosedExpr
tree Zero = Val  Zero
tree (Succ n) = Let (tree n) (λ shared -> Add (Var shared) (Var shared))

-- Observe sharing
text : ClosedExpr -> S.String
text e = go e Zero
         where
         go : Expr S.String -> Nat -> S.String
         go (Val x) _ = showNat x
         go (Add e₁ e₂) n = "(" S.++ (go e₁ n) S.++ " + " S.++ (go e₂ n) S.++ ")"
         go (Var x) n = x
         go (Let e₁ e₂) n with ("v" S.++ showNat n)
         ... | v = "let " S.++ v S.++ " = " S.++ (go e₁ (Succ n)) S.++
                        " in " S.++ (go (e₂ v) (Succ n)) S.++ ")"  

-- Remove sharing
inline : {a : Set} -> Expr (Expr a) -> Expr a
inline (Val i) = Val i
inline (Add e₁ e₂) = Add (inline e₁) (inline  e₂)
inline (Var x) = x
inline (Let e₁ e₂) = inline (e₂ (inline e₁))

-- Constant folding
remAdd : Expr Nat -> Expr Nat
remAdd (Val x) = Val x
remAdd (Add e₁ e₂) = Val (eval (remAdd e₁) + eval (remAdd e₂))
remAdd (Var x) = Var x
remAdd (Let e x) = Let (remAdd e) (λ x₁ → remAdd (x x₁))

-------------------------------------------------------------
-- Relations on Var-types
-------------------------------------------------------------

data _≃_ : Nat -> Expr Nat -> Set where
  Eq : ∀ {e n}  ->  n ≡ eval e -> n ≃ e

data _⋍_ : ∀ {n} -> Fin n -> Unit -> Set where
  Eq : ∀ {n} {f : Fin n} -> f ⋍ unit

--data _≂_ : ∀ {n} -> Fin n -> Nat -> Set where
--  Eq : ∀ {n m} {f : Fin n} -> (∀ {h : Stack n} -> lookup f h ≡ m) -> f ≂ m

_≂_ : ∀ {n} -> {s : Stack n} -> Fin n -> Nat -> Set
_≂_ {n} {s} i m = lookup i s ≡ m

-------------------------------------------------------------
-- Proofs
-------------------------------------------------------------
lem1 : {A B C D : Nat} -> A ≡ B -> C ≡ D -> A + C ≡ B + D
lem1 refl refl = refl

-- Constant folding does not change the value of an expression
remAddEquality' : {e : Expr Nat} -> eval e ≡ eval (remAdd e)
remAddEquality' {Val x} = refl
remAddEquality' {Add e e₁} with lem1 (remAddEquality' {e}) (remAddEquality' {e₁})
... | l = l
remAddEquality' {Var x} = refl
remAddEquality' {Let e x} with (cong x (remAddEquality' {e}))
... | q rewrite q = remAddEquality' {x (eval (remAdd e))}

remAddEquality : {e : ClosedExpr} -> eval e ≡ eval (remAdd e)
remAddEquality {e} = remAddEquality' {e {Nat}}

-- Removing sharing does not change the value of an expression
inlineEquality' : ∀ {eA : Expr Nat} {eB : Expr (Expr Nat)}
  -> _≃_ ⊢ eA ≡ eB -> (eval eA) ≡ (eval (inline  eB))
inlineEquality' Val = refl
inlineEquality' (Add p p₁) = lem (inlineEquality' p) (inlineEquality' p₁)
  where lem : {a b a' b' : Nat} -> a ≡ a' -> b ≡ b' -> a + b ≡ a' + b'
        lem refl refl = refl
inlineEquality' (Var (Eq x)) = x
inlineEquality' {Let x₁ e₁} {Let x₂ e₂} (Let p₁ p₂) with (p₂ {eval x₁} {inline (x₂)})
... | q = inlineEquality' (q (Eq (inlineEquality' p₁)))


inlineEquality : {e : ClosedExpr} -> eval e ≡ eval (inline e)
inlineEquality {e} = inlineEquality' ( e≡e {Nat} {Expr Nat} {_} {e})

-------------------------------------------------------------
-- Compiler
-------------------------------------------------------------

-- Data type for operations
data Op : Nat -> Nat -> Nat -> Set where
  Stop  : ∀ {n m} -> Op m n n
  Push  : ∀ {n m v} -> Nat -> Op v (Succ n) m -> Op v n m 
  Add   : ∀ {n m v} -> Op v (Succ n) m -> Op v (Succ (Succ n)) m
  Load  : ∀ {n m v} -> Fin v -> Op  v (Succ n) m -> Op v n m
  Store : ∀ {n m v} -> Fin v -> Op v n m -> Op v (Succ n) m

-- Concatenating operations
_++_ : ∀ {n m p v} -> Op v n m -> Op v m p -> Op v n p
Stop ++ o₂ = o₂
Push x o₁ ++ o₂ = Push x (o₁ ++ o₂)
Add o₁ ++ o₂ = Add (o₁ ++ o₂)
Load x o₁ ++ o₂ = Load x (o₁ ++ o₂)
Store x o₁ ++ o₂ = Store x (o₁ ++ o₂) 

++-assoc : ∀ {v n m p r : Nat} {op₁ : Op v n m} {op₂ : Op v m p} {op₃ : Op v p r} -> op₁ ++ (op₂ ++ op₃) ≡ (op₁ ++ op₂) ++ op₃
++-assoc {op₁ = Stop} = refl
++-assoc {op₁ = Push x op₁} {op₂} {op₃} = cong (λ x₁ → Push x x₁) (++-assoc {op₁ = op₁})
++-assoc {op₁ = Add op₁} = cong (λ x → Add x) (++-assoc {op₁ = op₁})
++-assoc {op₁ = Load x op₁} = cong (λ x₁ → Load x x₁) (++-assoc {op₁ = op₁})
++-assoc {op₁ = Store x op₁} = cong (λ x₁ → Store x x₁) (++-assoc {op₁ = op₁})

-- Executing an operation
exec : ∀ {n m v } -> Op v n m -> Stack n × Stack v -> Stack m × Stack v
exec Stop s = s
exec (Push x o) (x₁ , x₂) = exec o ((x ▻ x₁) , x₂)
exec (Add o) ((x ▻ (x₁ ▻ x₂)) , x₃) = exec o (((x + x₁) ▻ x₂) , x₃)
exec (Load x o) (x₁ , x₂) = exec o (((lookup x x₂) ▻ x₁ ), x₂ )
exec (Store x o) ((x₁ ▻ x₂) , x₃) = exec o (x₂ , update x x₁ x₃)

compile' : ∀ {v n} (t : Fin v) -> Expr (Fin v) -> Op v n (Succ n)
compile' t (Val m)      = Push m Stop
compile' t (Add e₁ e₂)  = compile' t e₁ ++ (compile' t e₂ ++ Add Stop)
compile' t (Var i)      = Load i Stop
compile' t (Let x e)    = compile' t x ++ Store t (compile' (predFin t) (e t))

compile : ∀ {v n} -> Expr (Fin (Succ v)) -> Op (Succ v) n (Succ n)
compile {v}  e = compile' (fromNat v) e

-------------------------------------------------------------
-- Example experssions
-------------------------------------------------------------

expr1 : ClosedExpr
expr1 = Let (Val (Succ Zero)) (λ i -> Add (Var i) (Var i))

expr2 : ClosedExpr
expr2 = Let (Val (Succ Zero)) (λ i -> Let (Val (Succ (Succ Zero)))(λ ii -> Add (Var i) (Var ii)))

expr3 : ClosedExpr
expr3 = Add (Let (Val (Succ Zero)) (λ i -> Var i)) (Let (Val (Succ (Succ Zero))) (λ ii → Var ii))

test : ClosedExpr -> Nat
test e with (#vars e)
... | v with exec (compile {#vars e} (e )) (Empty , initHeap (Succ (#vars e)))
test e | v | x , x₁ = pop x

testop : ∀ {v n} -> Op v n (Succ n)
testop = Push (Succ Zero) (Push (Succ (Succ Zero)) (Add Stop))

testop2 :  ∀ {v n} -> Op v n (Succ n)
testop2 = Push (Succ Zero) Stop ++ (Push (Succ (Succ Zero)) Stop  ++ Add Stop)

-------------------------------------------------------------
-- Compiler correctness
-------------------------------------------------------------

lem : ∀ {n m p v} {op₁ : Op v n m} {op₂ : Op v m p}  {s : Stack n} {h : Stack v} -> exec op₂ (exec op₁ (s , h)) ≡ exec (op₁ ++ op₂) (s , h)
lem {op₁ = Stop} = refl
lem {op₁ = Push x op₁} = lem {op₁ = op₁}
lem {op₁ = Add op₁} {s = x ▻ (x₁ ▻ s)} = lem {op₁ = op₁}
lem {op₁ = Load x op₁} = lem {op₁ = op₁}
lem {op₁ = Store x op₁} {s = x₁ ▻ s} = lem {op₁ = op₁}

lem₁ : ∀ {n v n₁ n₂} {op₁ : Op v n (Succ n)} {op₂ : Op v (Succ n) (Succ (Succ n))}  {s : Stack n} {h h₁ h₂ : Stack v}
  -> exec op₁ (s , h) ≡ (n₁ ▻ s) , h₁ -> exec op₂ ((n₁ ▻ s) , h₁) ≡ (n₂ ▻ (n₁ ▻ s)) , h₂ -> exec (op₁ ++ op₂) (s , h) ≡ (n₂ ▻ (n₁ ▻ s)) , h₂
lem₁ {op₁ = op₁} {op₂ = op₂} {s = s} {h = h} p₁ p₂ rewrite ≡-symm (lem {op₁ = op₁} {op₂ = op₂} {s = s} {h = h}) with p₂
... | r rewrite ≡-symm p₁ = p₂

data Exists (A : Set) (B : A -> Set) : Set where
  ∃_,_ : (x : A) -> B x -> Exists A B

+-comm : ∀ {a b} -> a + b ≡ b + a
+-comm {b = Zero} = +Zero
  where +Zero : ∀ {a} -> a + Zero ≡ a
        +Zero {Zero} = refl
        +Zero {Succ a} = cong Succ +Zero
+-comm {a} {b = Succ b} rewrite +-comm {b} {a} = +-Succ {a} {b}
  where +-Succ : ∀ {a b} -> a + Succ b ≡ Succ (a + b)
        +-Succ {Zero} = refl
        +-Succ {Succ a₁} = cong Succ (+-Succ {a₁})

cC : ∀ {v n : Nat} {h h₁ : Stack (Succ v)} {s : Stack n} {eF : Expr (Fin (Succ v))} {eN : Expr Nat} {f : Fin (Succ v)}
  -> (_≂_ {Succ v} {h}) ⊢ eF ≡ eN ->  Exists (Stack (Succ v)) (λ h₁ -> exec (compile' f eF) (s , h) ≡ (eval eN ▻ s) , h₁)
cC {h = h} Val = ∃ h , refl
cC {v} {n} {h = h} {s = s} {eF = Add fₗ fᵣ} {eN = Add nₗ nᵣ} {f = f} (Add p p₁)
  rewrite ++-assoc {v = Succ v} {n = n} {m = Succ n} {op₁ = compile' f fₗ} {op₂ = compile' f fᵣ} {op₃ = Add Stop}
  with lem  {op₁ = compile' {n = n} f fₗ ++ compile' f fᵣ} {op₂ = Add Stop} {s = s} {h = h}
... | lemApp rewrite  ≡-symm lemApp  with (exec (compile' f fₗ) (s , h))
... | (sₗ , hₗ) with (exec (compile' f fᵣ) (sₗ , hₗ))
... | (sᵣ , hᵣ) with  (cC {v} {h = h} {h₁ = hₗ} {s = s} {f = f} p)
... | ∃ ehₗ , ccₗ with  cC {v} {h = {!ehₗ!}} p₁ --cC {v} {h = ehₗ} {h₁ = hᵣ} {s = eval nₗ ▻ s} {f = f} {!p₁!} -- p₁
... | ∃ ehᵣ , ccᵣ rewrite lem₁ {op₁ = compile' f fₗ} {op₂ = compile' f fᵣ} {s = s} {h = h} {h₁ = ehₗ} {h₂ = ehᵣ} ccₗ {!!} with +-comm {eval nᵣ} {eval nₗ}
... | comm rewrite comm = ∃ ehᵣ , {!!} --refl
cC {h = h} {eF = Var xf} {eN = Var xn} (Var x₁) rewrite x₁ = ∃ h , refl
cC {v} {n} {h = h} {s = s} {eF = Let b₁ e₁} {eN = Let b₂ e₂} {f = f} (Let p x) 
  rewrite ≡-symm (lem {op₁ = compile' {n = n} f b₁} {op₂ = Store f (compile' (predFin f) (e₁ f))} {s = s} {h = h})
  with (cC {v} {h = h} {h₁ = snd (exec (compile' f b₁) (s , h))} {s = s} {f = f} p)
... | ∃ eh₁ , cC₁ rewrite cC₁ with x {f} {eval b₂} ({!!}) -- ?! Fix ≂!
... | nope with cC {v} {h = update f (eval b₂) eh₁} {h₁ = snd (exec (compile' (predFin f) (e₁ f)) (s , update f (eval b₂) eh₁))} {s = s} {f = predFin f} {!!} --nope
... | ∃ eh₂ , cC₂ = ∃ eh₂ , cC₂

compilerCorrectness : ∀ {e : ClosedExpr} {n : Nat} {s : Stack n} {h : Stack (Succ (#vars e))} -> (fst (exec (compile e) (s , h))) ≡ eval e ▻ s
compilerCorrectness {e} {n} {s} {h} with cC {#vars e} {n} {h} {snd (exec (compile e) (s , h))} {s} {e} {e} {fromNat (#vars e)} (e≡e {Fin (Succ (#vars e))} {Nat} {_≂_} {e})
compilerCorrectness | ∃ x , x₁ rewrite x₁ = refl

