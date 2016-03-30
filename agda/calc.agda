open import Prelude
open import List

module calc where
  data τ : Set where
    unit : τ
    _⊗_  : τ → τ → τ
    _⊕_  : τ → τ → τ

  data var : Set where
    V : var

  _,,_ : {A : Set} → List A → A → List A
  L ,, x = x :: L

  · : {A : Set} → List A
  · = []

  data exp : Set where
    <>     : exp
    <_,_>  : exp → exp → exp
    fst    : exp → exp
    snd    : exp → exp
    inl    : exp → exp
    inr    : exp → exp
    case   : exp → (var × exp) → (var × exp) → exp

  data _⊢_::_ : List (var × τ) → exp → τ → Set where
    TUnit  : {Γ : List (var × τ)} → Γ ⊢ <> :: unit
    TProd  : {Γ : List (var × τ)} {e1 e2 : exp} {t1 t2 : τ} →
                 (D1 : Γ ⊢ e1 :: t1) →
                 (D2 : Γ ⊢ e2 :: t2) →
                 Γ ⊢ < e1 , e2 > :: (t1 ⊗ t2)
    TFst   : {Γ : List (var × τ)} {e : exp} {t1 t2 : τ} →
                 (D : Γ ⊢ e :: (t1 ⊗ t2)) →
                 Γ ⊢ fst e :: t1
    TSnd   : {Γ : List (var × τ)} {e : exp} {t1 t2 : τ} →
                 (D : Γ ⊢ e :: (t1 ⊗ t2)) →
                 Γ ⊢ snd e :: t2
    TInl   : {Γ : List (var × τ)} {e : exp} {t1 t2 : τ} →
                 (D : Γ ⊢ e :: t1) →
                 Γ ⊢ inl e :: (t1 ⊕ t2)
    TInr   : {Γ : List (var × τ)} {e : exp} {t1 t2 : τ} →
                 (D : Γ ⊢ e :: t2) →
                 Γ ⊢ inr e :: (t1 ⊕ t2)
    TCase  : {Γ : List (var × τ)} {e : exp} {L R : var × exp} {t t1 t2 : τ} →
                 (D1 : Γ ⊢ e :: (t1 ⊕ t2)) →
                 (D2 : (Γ ,, (π1 L , t1)) ⊢ π2 L :: t) →
                 (D3 : (Γ ,, (π1 R , t2)) ⊢ π2 R :: t) →
                 Γ ⊢ case e L R :: t

  ex1 : · ⊢ fst < <> , <> > :: unit
  ex1 = TFst (TProd TUnit TUnit)

  -- ex2 : · ⊢ case (inl <>) (V , {!!}) (V , {!!}) :: unit
  -- ex2 = {!!}


    -- so this is the direct encoding. it ends up being really stupid to
    -- write tc, you need a maybe sigma deriv. instead, let's push the
    -- derivations into the same formation as the typing .. and i guess
     -- kind of exp forming

  -- tc : (e : exp) → Σ[ t ∈ τ ] (deriv e t)
  -- tc <> = unit , TUnit
  -- tc < e1 , e2 > with tc e1 | tc e2
  -- ... | (t1 , d1) | (t2 , d2) = prod t1 t2 , TProd d1 d2
  -- tc (fst e) = {!!} , (TFst {!!})
  -- tc (snd e) = {!!} , (TSnd {!!})
  -- tc (inl e) with tc e
  -- ... | (t , d) = sum t {!!} , TInl d
  -- tc (inr e) with tc e
  -- ... | (t , d) = sum {!!} t ,  TInr d
  -- tc (case e l r) with tc e
  -- tc (case e l r) | unit , d = {!!}
  -- tc (case e l r) | prod t t₁ , d = {!!}
  -- tc (case e l r) | sum t1 t2 , d = {!!}

  -- d : deriv < <> , <> > (prod unit unit)
  -- d = TProd TUnit TUnit
