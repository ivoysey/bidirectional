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
    X      : var → exp
    <_,_>  : exp → exp → exp
    fst    : exp → exp
    snd    : exp → exp
    inl    : exp → exp
    inr    : exp → exp
    case   : exp → (var × exp) → (var × exp) → exp

  data _⊢_::_ : List (var × τ) → exp → τ → Set where
    TUnit  : {Γ : List (var × τ)} → Γ ⊢ <> :: unit
    TX     : {Γ : List (var × τ)} {v : var} {t : τ} (p : (v , t) ∈ Γ ) →
                 Γ ⊢ (X v) :: t
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

  val : exp → Set
  val <> = ⊤
  val (X x) = ⊥
  val < e1 , e2 > = val e1 × val e2
  val (fst e) = ⊥ -- is this right?
  val (snd e) = ⊥ -- is this right?
  val (inl e) = val e
  val (inr e) = val e
  val (case e x x₁) = ⊥

  ex1 : · ⊢ fst < <> , <> > :: unit
  ex1 = TFst (TProd TUnit TUnit)

  ex2 : · ⊢ case (inl <>) (V , fst < X V , <> >) (V , <>) :: unit
  ex2 = TCase {t2 = unit} (TInl TUnit) (TFst (TProd (TX ∈h) TUnit)) TUnit

  step : (e : exp) (t : τ) (Γ : List (var × τ)) (D : Γ ⊢ e :: t) → exp
  step = {!!}
