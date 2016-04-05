open import Prelude
open import List
open import Nat

module calc where
  -- some cute notation for variables
  data var : Set where
    V : Nat → var

  -- even cuter notation for context maniupulation. the real reason that
  -- contexts act correctly (i.e. has the right structrual properties of
  -- weakening, contraction, and exchange) is found in the List file; we
  -- force membership at the type level below using the relation ∈, which
  -- doesn't care about duplicate or order.
  _,,_ : {A : Set} → List A → A → List A
  L ,, x = x :: L

  · : {A : Set} → List A
  · = []

  -- pretty raw grammar of types
  data τ : Set where
    unit : τ
    void : τ
    _⊗_  : τ → τ → τ
    _⊕_  : τ → τ → τ

  -- pretty raw grammar of expressions
  data exp : Set where
    -- variables
    X      : var → exp
    -- multiplicative fragment
    <>     : exp        -- intro form of unit, so no elim
    <_,_>  : exp → exp → exp
    fst    : exp → exp
    snd    : exp → exp
    -- additive fragment
    !!     : exp → exp  -- elim form of void, so no intro
    inl    : exp → exp
    inr    : exp → exp
    case   : exp → (var × exp) → (var × exp) → exp

  -- typechecking rules for declarative system
  data _⊢_::_ : List (var × τ) → exp → τ → Set where
    -- structural rules
    TX     : {Γ : List (var × τ)} {v : var} {t : τ} (p : (v , t) ∈ Γ ) →
                 Γ ⊢ (X v) :: t
    -- multiplicative fragment
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
    -- additive fragment
    TAbort : {Γ : List (var × τ)} {e : exp} {t : τ} →
                 Γ ⊢ e :: void →
                 Γ ⊢ (!! e) :: t
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

  -- a couple little derivations; note that agda's auto mode is strong
  -- enough to write these based on the constraints given by the rules
  -- above, including generating the list of bindings when going into the
  -- branch.
  ex1 : · ⊢ fst < <> , <> > :: unit
  ex1 = TFst (TProd TUnit TUnit)

  ex2 : · ⊢ case (inl <> )
                 (V 0 , fst < (X (V 0)) , <> >)
                 (V 1 , <>) :: unit
  ex2 = TCase {t2 = unit} (TInl TUnit) (TFst (TProd (TX ∈h) TUnit)) TUnit

  -- the value judgement
  val : exp → Set
  val <> = ⊤
  val (!! e) = {!!}
  val (X x) = ⊥
  val < e1 , e2 > = val e1 × val e2
  val (fst e) = ⊥ -- is this right?
  val (snd e) = ⊥ -- is this right?
  val (inl e) = val e
  val (inr e) = val e
  val (case e x x₁) = ⊥

  -- small step semantics. this is a little different than usual, kind
  -- of. we usually ignore the cases of expressions which aren't well typed
  -- when we're defining how programs step. the richer type of this
  -- function makes much more explicit so that we case on the derivation in
  -- each case and therefore don't have to write vacuous clauses for those
  -- expressions that don't even make sense or return an option.
  step : (e : exp) (t : τ) (Γ : List (var × τ)) (D : Γ ⊢ e :: t) (x : val e → ⊥) → exp
  step = {!!}
