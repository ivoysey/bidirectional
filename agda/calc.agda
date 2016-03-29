{-# OPTIONS --no-positivity-check #-}

open import Prelude
open import List

module calc where
  data τ : Set where
    unit : τ
    prod : τ → τ → τ
    sum  : τ → τ → τ

  data exp : Set where
    <>     : exp
    <_,_>  : exp → exp → exp
    fst    : exp → exp
    snd    : exp → exp
    inl    : exp → exp
    inr    : exp → exp
    case   : exp → (exp → exp) → (exp → exp) → exp -- hmm

  -- data seq : Set where
  --   _⊢_::_ : List (exp × τ) → exp → τ → seq

  data _:-_ : exp → τ → Set where
    TUnit :  <> :- unit -- Γ ⊢ <> :: unit
    TProd : {e1 e2 : exp} {t1 t2 : τ} →
             e1 :- t1 →
             e2 :- t2 →
             < e1 , e2 > :- (prod t1 t2)
    TFst  : {e : exp} {t1 t2 : τ} →
            e :- (prod t1 t2) →
            (fst e) :- t1
    TSnd : {e : exp} {t1 t2 : τ} →
            e :- (prod t1 t2) →
            (snd e) :- t2
    TInl  : {e : exp} {t1 t2 : τ} →
            e :- t1 →
            (inl e) :- (sum t1 t2)
    TInr  : {e : exp} {t1 t2 : τ} →
              e :- t2 →
              (inr e) :- (sum t1 t2)
    TCase : {e : exp} {t1 t2 t : τ} {L R : exp → exp} →
             L e :- {!!} →
             R e :- {!!} →
             e :- (sum t1 t2) →
             case e {!(!} {!!} :- t


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
