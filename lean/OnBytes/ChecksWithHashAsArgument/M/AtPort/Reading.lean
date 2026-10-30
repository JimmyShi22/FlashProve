-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/AtPort/Reading.lean: the twin over a monad, at the identity monad and the
program's hash, is the port's own text. The seeds, the place in the binding tree, the
readings that name their refusals, and a file's tail.
`RelP w w'`: each run of the twin's reading w (over the identity monad) is the run of the port's w'.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Chain
import OnBytes.ChecksWithHashAsArgument.M.Proof.ReadingHom
import OnBytes.ChecksWithHashAsArgument.M.Proof.Tail

set_option autoImplicit false

namespace OnBytes.TwoPort.M.AtPort

open OnBytes.Params (TableName IndexShape LinBindingShape)

/-! ## The seeds and the table's key -/

/-- At the identity monad "first x, then g" is g at x. For letters x and g: nothing is computed. -/
theorem idBind {α β : Type} (x : Id α) (g : α → Id β) : x >>= g = g x := rfl

/-- The first value of the seeds' chain at the format's own hash is the format's. -/
theorem recordFirstW_atH (name : ByteArray) :
    Fmt.recordFirstW (m := Id) Fmt.formatHash name = Fmt.recordFirst name := rfl

/-- A chain's step at the format's own hash is the format's. For a letter c: nothing is computed. -/
theorem queryW_atH (c : Fmt.Chain) (b : ByteArray) (kind : Fmt.Kind) (work nonce K : Nat) :
    Fmt.Chain.queryW (m := Id) Fmt.formatHash c b kind work nonce K = c.query b kind work nonce K := rfl

/-- `recordSeeds_port` as an equation of two functions. The port's `recordSeeds` is unfolded while
it stands alone, without arguments; every further step is a rewriting by a named equation; and a
letter q stands for the round's value before the two texts are compared. It is written so that no
checker need compute that value: a checker that is given the two texts at the value itself may
unfold the match in them, and then the round. -/
theorem recordSeeds_port_fn :
    (fun f name bits count => M.recordSeeds (m := Id) formatHashFastForm f name bits count) =
      OnBytes.recordSeeds := by
  delta OnBytes.recordSeeds
  funext f name bits count
  rw [M.recordSeeds, formatHashFastForm_eq_formatHash, idBind, idBind, recordFirstW_atH, queryW_atH]
  generalize Fmt.Chain.query _ _ _ _ _ _ = q
  cases q with
  | none => rfl
  | some p =>
    cases p
    rfl

theorem recordSeeds_port (f : Fmt.Fld) (name : ByteArray) (bits count : Nat) :
    M.recordSeeds (m := Id) formatHashFastForm f name bits count = OnBytes.recordSeeds f name bits count :=
  congrFun (congrFun (congrFun (congrFun recordSeeds_port_fn f) name) bits) count

theorem tableKey_port (f : Fmt.Fld) (cfg : ByteArray) (s : IndexShape) (table : TableName)
    (item : Nat) :
    M.tableKey (m := Id) formatHashFastForm f cfg s table item = OnBytes.tableKey f cfg s table item := by
  unfold M.tableKey OnBytes.tableKey
  simp only [recordSeeds_port]
  rfl

/-! ## The place -/

theorem climb_port (cfg b : ByteArray) :
    ∀ (levels : Nat) (x : ByteArray) (p i : Nat),
      M.Proof.climb (m := Id) formatHashFastForm cfg b levels x p i = OnBytes.Proof.climb cfg b levels x p i
  | 0, _, _, _ => rfl
  | levels + 1, x, p, i => by
    unfold M.Proof.climb OnBytes.Proof.climb
    cases Fmt.slice b i 32 with
    | none => rfl
    | some sib =>
      dsimp only
      by_cases hp : (p % 2 == 1) = true
      · simp only [if_pos hp]
        show M.Proof.climb (m := Id) formatHashFastForm cfg b levels (Fmt.vertexBW (m := Id) formatHashFastForm cfg sib x)
          (p / 2) (i + 32) = _
        rw [climb_port cfg b levels, formatHashFastForm_eq_formatHash]
        rfl
      · simp only [if_neg hp]
        show M.Proof.climb (m := Id) formatHashFastForm cfg b levels (Fmt.vertexBW (m := Id) formatHashFastForm cfg x sib)
          (p / 2) (i + 32) = _
        rw [climb_port cfg b levels, formatHashFastForm_eq_formatHash]
        rfl

theorem readPlace_port (s : LinBindingShape) (cfg closing b : ByteArray) (i : Nat) :
    M.Proof.readPlace (m := Id) formatHashFastForm s cfg closing b i =
      OnBytes.Proof.readPlace s cfg closing b i := by
  unfold M.Proof.readPlace OnBytes.Proof.readPlace
  split
  · rfl
  · cases Fmt.rdWord b i with
    | none => rfl
    | some y =>
      obtain ⟨w, i1⟩ := y
      dsimp only
      split
      · rfl
      · cases Fmt.slice b i1 s.saltBytes with
        | none => rfl
        | some salt =>
          show Option.map _ (M.Proof.climb (m := Id) formatHashFastForm cfg b s.logLeaves
            (Fmt.bindLeafW (m := Id) formatHashFastForm s.logLeaves w.toNat cfg closing salt) w.toNat
            (i1 + s.saltBytes)) = _
          rw [climb_port, formatHashFastForm_eq_formatHash]
          rfl

/-! ## Readings -/

/-- Each run of the twin's reading is the run of the port's. -/
def RelP {α : Type} (w : M.Proof.Reading Id α) (w' : OnBytes.Proof.Reading α) : Prop :=
  ∀ s, (w s).run = w' s

theorem relP_pure {α : Type} (a : α) :
    RelP (pure a : M.Proof.Reading Id α) (pure a : OnBytes.Proof.Reading α) := fun _ => rfl

theorem relP_throw {α : Type} (e : String) :
    RelP (throw e : M.Proof.Reading Id α) (throw e : OnBytes.Proof.Reading α) := fun _ => rfl

theorem relP_bind {α β : Type} {w : M.Proof.Reading Id α} {w' : OnBytes.Proof.Reading α}
    {g : α → M.Proof.Reading Id β} {g' : α → OnBytes.Proof.Reading β} (hw : RelP w w')
    (hg : ∀ a, RelP (g a) (g' a)) : RelP (w >>= g) (w' >>= g') := by
  intro s
  rw [M.Proof.Reading.run_bind, hw s]
  show (match w' s with
    | .ok p => (g p.1 p.2).run
    | .error e => (pure (Except.error e) : Id (Except String (β × Session)))) =
      (w' s).bind fun p => g' p.1 p.2
  cases w' s with
  | ok p => exact hg p.1 p.2
  | error e => rfl

theorem relP_need {α : Type} (why : String) (x : Option α) :
    RelP (M.Proof.need (m := Id) why x) (OnBytes.Proof.need why x) := by
  intro s
  cases x <;> rfl

theorem relP_needM {α : Type} (why : String) {x : Id (Option α)} {x' : Option α} (hx : x = x') :
    RelP (M.Proof.needM (m := Id) why x) (OnBytes.Proof.need why x') := by
  subst hx
  intro s
  show (match x with
    | none => _
    | some a => _) = _
  cases x <;> rfl

theorem readerName_port (front : String) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray)
    (i : Nat) :
    M.Proof.readerName (m := Id) formatHashFastForm front S seen b i =
      OnBytes.Proof.readerName front S seen b i := by
  unfold M.Proof.readerName OnBytes.Proof.readerName
  show (match M.whyRefused (m := Id) formatHashFastForm S seen b i with
    | some (k, _) => _
    | none => _) = _
  rw [whyRefused_port]
  cases OnBytes.whyRefused S seen b i <;> rfl

theorem relP_readNamed (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    RelP (M.Proof.readNamed (m := Id) formatHashFastForm front S b i) (OnBytes.Proof.readNamed front S b i) := by
  intro s
  unfold M.Proof.readNamed OnBytes.Proof.readNamed
  show (match (M.readIn (m := Id) formatHashFastForm S b i s).run with
    | some y => _
    | none => _) = _
  rw [readIn_port]
  cases OnBytes.readIn S b i s with
  | some y => rfl
  | none =>
    show Except.error (M.Proof.readerName (m := Id) formatHashFastForm front S s.seen b i) = _
    rw [readerName_port]
    rfl

theorem fromStart_port {α : Type} {w : M.Proof.Reading Id α} {w' : OnBytes.Proof.Reading α}
    (hw : RelP w w') : M.Proof.Reading.fromStart w = OnBytes.Proof.Reading.fromStart w' := by
  unfold M.Proof.Reading.fromStart OnBytes.Proof.Reading.fromStart
  show Except.map _ (w Session.start).run = _
  rw [hw]

/-! ## The tail -/

theorem relP_readTail (p : OnBytes.Proof.TailPublic) (dry : OnBytes.Proof.FirstEnd)
    (first : ChainRead) (b : ByteArray) :
    RelP (M.Proof.readTail (m := Id) formatHashFastForm p dry first b)
      (OnBytes.Proof.readTail p dry first b) := by
  unfold M.Proof.readTail OnBytes.Proof.readTail
  dsimp only
  refine relP_bind (relP_need _ _) fun seal1 => ?_
  refine relP_bind (relP_needM _ (readPlace_port _ _ _ _ _)) fun place => ?_
  refine relP_bind (relP_needM _ (tableKey_port _ _ _ _ _)) fun key => ?_
  refine relP_bind (relP_need _ _) fun x => ?_
  obtain ⟨rounds2, end2⟩ := x
  refine relP_bind (relP_need _ _) fun spec2 => ?_
  refine relP_bind (relP_readNamed _ _ _ _) fun shared => ?_
  refine relP_bind (relP_need _ _) fun seal2 => ?_
  refine relP_bind (relP_need _ _) fun rounds3 => ?_
  refine relP_bind (relP_need _ _) fun spec3 => ?_
  refine relP_bind (relP_readNamed _ _ _ _) fun second => ?_
  exact relP_pure _

end OnBytes.TwoPort.M.AtPort
