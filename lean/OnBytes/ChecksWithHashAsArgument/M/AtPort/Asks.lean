-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean: how many questions the twin's readings of a key file and of a
proof file ask. After the pattern of Entry/RoadCost.lean.
`LeR c w t P`: every run of the reading w costs at most t, and what it returns has P.
The numbers are in units of k, the cost of one call of the hash. A chain with the description S
costs `fileNX S` (OnBytes/Tie/CostX.lean), and twice that under `readNamed`, which goes over a
refused chain a second time. The descriptions of the later chains are made from what was read, so
the bounds take, as hypotheses, a number for each chain that holds whatever was read.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.Entry.RoadCostLands
import OnBytes.ChecksWithHashAsArgument.M.Proof.ReadingHom
import OnBytes.ChecksWithHashAsArgument.M.Proof.File
import OnBytes.ChecksWithHashAsArgument.M.Key.File

set_option autoImplicit false

namespace OnBytes.TwoPort.M.Asks

open OnBytes.Tie.CostX
open OnBytes.Params (TableName KeyChains ProofChains LinBindingShape)

variable {m : Type → Type} [Monad m] (c : Run.CostP m) (k : Nat)

/-- Every run of w costs at most t, and a value that it returns has P. -/
def LeR {α : Type} (w : M.Proof.Reading m α) (t : Nat) (P : α → Prop) : Prop :=
  ∀ s, c.le (w s).run t fun r => ∀ a s', r = .ok (a, s') → P a

theorem leR_pure {α : Type} (a : α) (P : α → Prop) (h : P a) :
    LeR c (pure a : M.Proof.Reading m α) 0 P := by
  intro s
  refine c.le_pure _ _ ?_
  intro a' s' e
  cases e
  exact h

theorem leR_mono {α : Type} {w : M.Proof.Reading m α} {t t' : Nat} {P Q : α → Prop}
    (hw : LeR c w t P) (ht : t ≤ t') (hP : ∀ a, P a → Q a) : LeR c w t' Q :=
  fun s => c.le_mono _ _ _ _ _ (hw s) ht fun _ h a s' e => hP a (h a s' e)

theorem leR_bind {α β : Type} {w : M.Proof.Reading m α} {g : α → M.Proof.Reading m β}
    {t t' : Nat} {P : α → Prop} {Q : β → Prop} (hw : LeR c w t P)
    (hg : ∀ a, P a → LeR c (g a) t' Q) : LeR c (w >>= g) (t + t') Q := by
  intro s
  rw [M.Proof.Reading.run_bind]
  refine c.le_bind _ _ _ _ _ _ (hw s) fun r hr => ?_
  cases r with
  | ok p => exact hg p.1 (hr p.1 p.2 rfl) p.2
  | error e =>
    refine Run.CostP.pureLe c _ _ _ ?_
    intro a s' h
    cases h

theorem leR_throw {α : Type} (e : String) (P : α → Prop) :
    LeR c (throw e : M.Proof.Reading m α) 0 P := by
  intro s
  show c.le ((pure (Except.error e) : m (Except String α)) >>=
      ExceptT.bindCont (fun a => (pure (a, s) : ExceptT String m (α × Session)))) 0 _
  refine c.le_bind _ _ 0 0 (fun r => r = .error e) _ (c.le_pure _ _ rfl) fun r hr => ?_
  subst hr
  refine c.le_pure _ _ ?_
  intro a s' h
  cases h

theorem leR_need {α : Type} (why : String) (x : Option α) :
    LeR c (M.Proof.need (m := m) why x) 0 fun a => x = some a := by
  intro s
  unfold M.Proof.need
  simp only [ExceptT.run_mk]
  refine c.le_pure _ _ ?_
  intro a s' h
  cases x with
  | none => cases h
  | some y =>
    cases h
    rfl

theorem leR_needM {α : Type} (why : String) {x : m (Option α)} {t : Nat}
    (hx : c.le x t fun _ => True) : LeR c (M.Proof.needM why x) t fun _ => True :=
  fun s => c.le_mono _ _ _ _ _ (RoadCost.le_needM c why x t hx s) (Nat.le_refl _)
    fun _ _ _ _ _ => trivial

/-- The same, with what is known of the value handed on. -/
theorem leR_needM' {α : Type} (why : String) {x : m (Option α)} {t : Nat} {P : α → Prop}
    (hx : c.le x t fun r => ∀ a, r = some a → P a) : LeR c (M.Proof.needM why x) t P := by
  intro s
  unfold M.Proof.needM
  simp only [ExceptT.run_mk]
  refine c.le_bind _ _ t 0 _ _ hx fun r hr => ?_
  cases r with
  | none =>
    refine c.le_pure _ _ ?_
    intro a s' e
    cases e
  | some y =>
    refine c.le_pure _ _ ?_
    intro a s' e
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Except.ok.inj e)
    exact hr _ rfl

theorem leR_guard {β : Type} {p : Prop} [Decidable p] (e : String)
    {g : PUnit → M.Proof.Reading m β} {t : Nat} {Q : β → Prop} (hg : ∀ y, LeR c (g y) t Q) :
    LeR c (if p then throw e >>= g else pure PUnit.unit >>= g) t Q := by
  split
  · exact leR_mono c (leR_bind c (leR_throw c e fun _ => True) fun y _ => hg y) (by omega)
      fun _ h => h
  · exact leR_mono c (leR_bind c (leR_pure c _ (fun _ => True) trivial) fun y _ => hg y) (by omega)
      fun _ h => h

variable (h : HashM m)
  (hk : ∀ number tree index start bytes, c.le (h number tree index start bytes) k fun _ => True)
include hk

theorem leR_readNamed (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) :
    LeR c (M.Proof.readNamed h front S b i) (2 * fileNX S * k) fun _ => True :=
  fun s => c.le_mono _ _ _ _ _ (RoadCost.le_readNamed c k h hk front S b i s)
    (by rw [Nat.mul_assoc, Nat.two_mul]) fun _ _ _ _ _ => trivial

/-! ## The place in the binding tree -/

theorem le_climb (cfg b : ByteArray) :
    ∀ (levels : Nat) (x : ByteArray) (p i : Nat),
      c.le (M.Proof.climb h cfg b levels x p i) (levels * k) fun _ => True
  | 0, _, _, _ => by
    rw [Nat.zero_mul]
    exact c.le_pure _ _ trivial
  | levels + 1, x, p, i => by
    unfold M.Proof.climb
    split
    · exact Run.CostP.pureLe c _ _ _ trivial
    · dsimp only
      refine c.le_mono _ (k + levels * k) _ _ _ ?_ (by rw [Nat.add_mul]; omega) fun _ h => h
      split <;> exact c.le_bind _ _ _ _ (fun _ => True) _ (hk _ _ _ _ _) fun _ _ =>
        le_climb cfg b levels _ _ _

theorem le_readPlace (s : LinBindingShape) (cfg closing b : ByteArray) (i : Nat) :
    c.le (M.Proof.readPlace h s cfg closing b i) ((1 + s.logLeaves) * k) fun _ => True := by
  unfold M.Proof.readPlace
  split
  · exact Run.CostP.pureLe c _ _ _ trivial
  · split
    · exact Run.CostP.pureLe c _ _ _ trivial
    · split
      · exact Run.CostP.pureLe c _ _ _ trivial
      · split
        · exact Run.CostP.pureLe c _ _ _ trivial
        · refine c.le_mono _ (k + (s.logLeaves * k + 0)) _ _ _ ?_
            (by rw [Nat.add_mul]; omega) fun _ h => h
          refine c.le_bind _ _ _ _ (fun _ => True) _ (hk _ _ _ _ _) fun leaf _ => ?_
          exact c.le_bind _ _ _ _ (fun _ => True) _ (le_climb c k h hk _ _ _ _ _ _) fun _ _ =>
            c.le_pure _ _ trivial

/-- A key that `tableKey` returns fits the shape. -/
theorem le_tableKey_fits (f : Fmt.Fld) (cfg : ByteArray) (s : Params.IndexShape)
    (table : TableName) (item : Nat) :
    c.le (M.tableKey h f cfg s table item) (RoadCost.keyN s * k)
      fun r => ∀ key, r = some key → key.fits s = true ∧ key.item = item := by
  have fin : ∀ (seeds : Option (List (List E × E))) (key : TableKey),
      (seeds.bind fun seeds =>
        let key : TableKey :=
          { item := item, record := table.answers.toArray, seeds := seeds.map fun x => ⟨x.1, x.2⟩ }
        if key.fits s then some key else none) = some key →
        key.fits s = true ∧ key.item = item := by
    intro seeds key e
    cases seeds with
    | none => cases e
    | some sd =>
      simp only [Option.bind_some] at e
      split at e
      · rename_i hf
        obtain rfl := Option.some.inj e
        exact ⟨hf, rfl⟩
      · cases e
  unfold M.tableKey RoadCost.keyN
  dsimp only
  exact c.le_bind _ _ _ 0 _ _ (RoadCost.le_recordSeeds c k h hk _ _ _ _) fun sd _ =>
    c.le_pure _ _ (fin sd)

theorem leR_readNamed_le (front : String) (S : Fmt.SpecX) (b : ByteArray) (i : Nat) {N : Nat}
    (hN : fileNX S ≤ N) : LeR c (M.Proof.readNamed h front S b i) (2 * N * k) fun _ => True :=
  leR_mono c (leR_readNamed c k h hk front S b i)
    (Nat.mul_le_mul_right k (Nat.mul_le_mul_left 2 hN)) fun _ h => h

/-! ## A description's number is its rounds' number -/

omit hk h k c in
/-- All the fields of a description that `describeWith` has made. -/
theorem describeWith_fields {g : Params.Given} {label : Nat} {statement : ByteArray}
    {rand : Fmt.Rand} {r : Params.Rounds} {firstTree : Nat} {S : Fmt.SpecX}
    (e : Params.describeWith g label statement rand r firstTree = some S) :
    S.base.rounds = r.map (·.1) ∧ S.stored = r.map (·.2) ∧ S.base.cfg = g.cfg ∧
      S.base.plan = g.plan ∧ S.base.label = label ∧ S.base.statement = statement ∧
      S.base.rand = rand ∧ S.base.params = g.bytes := by
  unfold Params.describeWith Params.Given.describe at e
  dsimp only at e
  split at e
  · rw [← Option.some.inj e]
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases e

omit hk h k c in
/-- The number of a description that was made from the rounds r is 3 and r's number: whatever
the statement, the random bytes and the parameter bytes. -/
theorem fileNX_describeWith {g : Params.Given} {label : Nat} {statement : ByteArray}
    {rand : Fmt.Rand} {r : Params.Rounds} {firstTree : Nat} {S : Fmt.SpecX}
    (e : Params.describeWith g label statement rand r firstTree = some S) :
    fileNX S = 3 + roundsNX r := by
  obtain ⟨h1, h2, -⟩ := describeWith_fields e
  have hz : ∀ l : Params.Rounds, (l.map (·.1)).zip (l.map (·.2)) = l := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      show (a.1, a.2) :: (l.map (·.1)).zip (l.map (·.2)) = a :: l
      rw [ih]
  unfold fileNX
  rw [h1, h2, hz]

/-! ## The entry file's reading -/

omit hk h k c in
/-- If the link's block has the same rounds' number whatever the two keys, every description that
the reading of an entry file can make has 3 and that number. -/
theorem specsBelow_of_rounds (p : Params.Link) (first : TableName) (N : Nat)
    (hN : ∀ k0 k1 r, (linkVerify p.link k0 k1).rounds (OnBytes.Entry.start p) = some r →
      roundsNX r ≤ N) : RoadCost.SpecsBelow p first (3 + N) := by
  intro further k0 k1 spec e
  obtain ⟨r, hr, hd⟩ := Option.bind_eq_some_iff.1 e
  rw [fileNX_describeWith hd]
  exact Nat.add_le_add_left (hN k0 k1 r hr) 3

/-- N bounds the number of every description that the reading of an entry file can make: at two keys
that fit the tables' shape and name the items 0 and 1, as `tableKey` returns them. -/
def SpecsBelowFit (p : Params.Link) (first : TableName) (N : Nat) : Prop :=
  ∀ (further : TableName) (k0 k1 : TableKey) (spec : Fmt.SpecX),
    k0.fits p.link.table = true → k1.fits p.link.table = true → k0.item = 0 → k1.item = 1 →
    ((linkVerify p.link k0 k1).rounds (OnBytes.Entry.start p)).bind (p.describe first further) =
      some spec → fileNX spec ≤ N

theorem le_readFit (p : Params.Link) (first : TableName) (file : ByteArray) (N : Nat)
    (hN : SpecsBelowFit p first N) :
    c.le (M.Entry.read h p first file) ((2 * RoadCost.keyN p.link.table + 2 * N) * k)
      fun _ => True := by
  unfold M.Entry.read
  dsimp only
  split
  · exact Run.CostP.pureLe c _ _ _ trivial
  · split
    · exact Run.CostP.pureLe c _ _ _ trivial
    · split
      · exact Run.CostP.pureLe c _ _ _ trivial
      · refine c.le_mono _ (RoadCost.keyN p.link.table * k + (RoadCost.keyN p.link.table * k +
            (N * k + N * k + 0))) _ _ _
          (c.le_bind _ _ _ _ _ _ (le_tableKey_fits c k h hk _ _ _ _ _) fun a0 f0 =>
            c.le_bind _ _ _ _ _ _ (le_tableKey_fits c k h hk _ _ _ _ _) fun a1 f1 => ?_)
          (by simp only [Nat.add_mul, Nat.two_mul]; omega) fun _ h => h
        split
        · rename_i k0 k1
          split
          · exact Run.CostP.pureLe c _ _ _ trivial
          · rename_i spec hs
            have hle : fileNX spec * k ≤ N * k := Nat.mul_le_mul_right _
              (hN _ _ _ _ (f0 k0 rfl).1 (f1 k1 rfl).1 (f0 k0 rfl).2 (f1 k1 rfl).2 hs)
            refine c.le_bind _ _ _ 0 (fun _ => True) _
              (RoadCost.le_fromStart c _ _ fun s =>
                c.le_mono _ _ _ _ _ (RoadCost.le_readNamed c k h hk "" spec file _ s)
                  (Nat.add_le_add hle hle) fun _ h => h) fun r _ => ?_
            cases r <;> exact c.le_pure _ _ trivial
        · exact Run.CostP.pureLe c _ _ _ trivial

/-! ## The tail -/

open OnBytes.Proof (TailPublic FirstEnd TailRead sharedBlock sharedStart secondBlock secondStart
  secondFirstTree)

/-- N2 bounds the number of every description of the shared chain that `readTail` can make. -/
def SharedBelow (p : TailPublic) (N2 : Nat) : Prop :=
  ∀ key x root S, key.fits p.lin.fold.index = true →
    (sharedBlock p.lin key).dryRun (sharedStart p) = some x →
    p.shared.describe p.lab₂ p.table root x.1 = some S → fileNX S ≤ N2

/-- N3 bounds the number of every description of the second chain that `readTail` can make. -/
def SecondBelow (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (N3 : Nat) : Prop :=
  ∀ key x shared rounds3 seal1 seal2 S, key.fits p.lin.fold.index = true →
    (sharedBlock p.lin key).dryRun (sharedStart p) = some x →
    (secondBlock p.lin dry.lin (x.2.goesOn shared)).rounds (secondStart p dry first) =
      some rounds3 →
    p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree first) = some S → fileNX S ≤ N3

/-- The questions of a tail, in units of k. -/
def tailN (p : TailPublic) (N2 N3 : Nat) : Nat :=
  (1 + p.binding.logLeaves) + RoadCost.keyN p.lin.fold.index + 2 * N2 + 2 * N3

theorem leR_readTail (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray)
    {N2 N3 : Nat} (h2 : SharedBelow p N2) (h3 : SecondBelow p dry first N3) :
    LeR c (M.Proof.readTail h p dry first b) (tailN p N2 N3 * k) fun _ => True := by
  unfold M.Proof.readTail
  dsimp only
  refine leR_mono c (t := 0 + ((1 + p.binding.logLeaves) * k + (RoadCost.keyN p.lin.fold.index * k +
    (0 + (0 + (2 * N2 * k + (0 + (0 + (0 + (2 * N3 * k + 0)))))))))) ?_
    (by simp only [tailN, Nat.add_mul]; omega) fun _ h => h
  refine leR_bind c (leR_need c _ _) fun seal1 _ => ?_
  refine leR_bind c (leR_needM c _ (le_readPlace c k h hk _ _ _ _ _)) fun place _ => ?_
  refine leR_bind c (leR_needM' c _ (le_tableKey_fits c k h hk _ _ _ _ _)) fun key hkey => ?_
  refine leR_bind c (leR_need c _ _) fun x hx => ?_
  obtain ⟨rounds2, end2⟩ := x
  refine leR_bind c (leR_need c _ _) fun spec2 hs2 => ?_
  refine leR_bind c (leR_readNamed_le c k h hk _ _ _ _ (h2 key _ _ _ hkey.1 hx hs2)) fun
      shared _ => ?_
  refine leR_bind c (leR_need c _ _) fun seal2 _ => ?_
  refine leR_bind c (leR_need c _ _) fun rounds3 hr3 => ?_
  refine leR_bind c (leR_need c _ _) fun spec3 hs3 => ?_
  refine leR_bind c (leR_readNamed_le c k h hk _ _ _ _ (h3 key _ shared _ _ _ _ hkey.1 hx hr3 hs3))
    fun second _ => ?_
  exact leR_pure c _ _ trivial

/-! ## The proof file -/

/-- N1 bounds the number of every description of the first chain that `readProof` can make. -/
def FirstBelow (cs : ProofChains) (table : TableName) (copy : Nat) (request words : ByteArray)
    (block : Blk FirstEnd) (N1 : Nat) : Prop :=
  ∀ x S, block.dryRun (OnBytes.Proof.firstStart cs.first) = some x →
    cs.first.describe table copy request words x.1 = some S → fileNX S ≤ N1

theorem leR_readProof (cs : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (block : Blk FirstEnd) (file : ByteArray) {N1 N2 N3 : Nat}
    (h1 : FirstBelow cs table copy request words block N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic cs table) N2)
    (h3 : ∀ x first, block.dryRun (OnBytes.Proof.firstStart cs.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic cs table) x.2 first N3) :
    LeR c (M.Proof.readProof h cs table copy request words block file)
      ((2 * N1 + tailN (OnBytes.Proof.tailPublic cs table) N2 N3) * k) fun _ => True := by
  unfold M.Proof.readProof
  dsimp only
  refine leR_mono c (t := 0 + (0 + (0 + (2 * N1 * k +
    (tailN (OnBytes.Proof.tailPublic cs table) N2 N3 * k + 0))))) ?_
    (by simp only [Nat.add_mul]; omega) fun _ h => h
  split <;> refine leR_bind c (P := fun _ => True)
    (by first | exact leR_throw c _ _ | exact leR_pure c _ _ trivial) fun x _ => ?_
  all_goals
    obtain ⟨madeOn, i⟩ := x
    dsimp only
    refine leR_guard c _ fun _ => ?_
    refine leR_guard c _ fun _ => ?_
    refine leR_bind c (leR_need c _ _) fun x hx => ?_
    obtain ⟨rounds1, dry⟩ := x
    refine leR_bind c (leR_need c _ _) fun spec1 hs1 => ?_
    refine leR_bind c (leR_readNamed_le c k h hk _ _ _ _ (h1 _ _ hx hs1)) fun first _ => ?_
    refine leR_bind c (leR_readTail c k h hk _ _ _ _ h2 (h3 _ _ hx)) fun r _ => ?_
    exact leR_guard c _ fun _ => leR_pure c _ _ trivial

omit hk in
theorem le_fromStart {α : Type} {w : M.Proof.Reading m α} {t : Nat} {P : α → Prop}
    (hw : LeR c w t P) : c.le (M.Proof.Reading.fromStart w) t fun _ => True :=
  RoadCost.le_fromStart c w t fun s => c.le_mono _ _ _ _ _ (hw s) (Nat.le_refl _) fun _ _ => trivial

theorem le_proofCheck (cs : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (reply : E) (links : Blk OnBytes.Proof.LinksResult) (file : ByteArray) {N1 N2 N3 : Nat}
    (h1 : FirstBelow cs table copy request words
      (OnBytes.Proof.firstBlock cs.first links reply) N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic cs table) N2)
    (h3 : ∀ x first, (OnBytes.Proof.firstBlock cs.first links reply).dryRun
        (OnBytes.Proof.firstStart cs.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic cs table) x.2 first N3) :
    c.le (M.Proof.check h cs table copy request words reply links file)
      ((2 * N1 + tailN (OnBytes.Proof.tailPublic cs table) N2 N3) * k) fun _ => True := by
  unfold M.Proof.check
  dsimp only
  refine c.le_bind _ _ _ 0 _ _
    (le_fromStart c (leR_readProof c k h hk cs table copy request words _ file h1 h2 h3)) fun r _ =>
      ?_
  cases r with
  | error why => exact c.le_pure _ _ trivial
  | ok r =>
    simp only []
    split <;> exact c.le_pure _ _ trivial

/-! ## The key file -/

/-- N1 bounds the number of every description of the one-time chain that `readKey` can make. -/
def OneTimeBelow (ks : KeyChains) (table : TableName) (N1 : Nat) : Prop :=
  ∀ x S, (OnBytes.Key.oneTime ks.oneTime).dryRun (OnBytes.Key.startOf ks.oneTime) = some x →
    ks.oneTime.describe table x.1 = some S → fileNX S ≤ N1

theorem leR_readKey (ks : KeyChains) (table : TableName) (file : ByteArray) (j : Nat)
    {N1 N2 N3 : Nat} (h1 : OneTimeBelow ks table N1)
    (h2 : SharedBelow (OnBytes.Key.tailPublic ks table) N2)
    (h3 : ∀ x first, (OnBytes.Key.oneTime ks.oneTime).dryRun (OnBytes.Key.startOf ks.oneTime) =
        some x → SecondBelow (OnBytes.Key.tailPublic ks table) x.2 first N3) :
    LeR c (M.Key.readKey h ks table file j)
      ((2 * N1 + tailN (OnBytes.Key.tailPublic ks table) N2 N3) * k) fun _ => True := by
  unfold M.Key.readKey
  dsimp only
  refine leR_mono c (t := 0 + (0 + (2 * N1 * k +
    (tailN (OnBytes.Key.tailPublic ks table) N2 N3 * k + 0)))) ?_
    (by simp only [Nat.add_mul]; omega) fun _ h => h
  refine leR_bind c (leR_need c _ _) fun x hx => ?_
  obtain ⟨rounds, dry⟩ := x
  refine leR_bind c (leR_need c _ _) fun spec hs => ?_
  refine leR_bind c (leR_readNamed_le c k h hk _ _ _ _ (h1 _ _ hx hs)) fun first _ => ?_
  refine leR_bind c (leR_readTail c k h hk _ _ _ _ h2 (h3 _ _ hx)) fun r _ => ?_
  exact leR_guard c _ fun _ => leR_pure c _ _ trivial

end OnBytes.TwoPort.M.Asks

namespace OnBytes.TwoPort.M.AsksLands

open _root_.ZKCP
open _root_.Run
open OnBytes.TwoPort.M.Asks
open OnBytes.Params (TableName KeyChains ProofChains)

/-- The reading of a proof file that asks the one oracle: no coin, and at most twice the number.
-/
theorem readProof_asks (cs : ProofChains) (table : TableName) (copy : Nat)
    (request words : ByteArray)
    (block : Blk OnBytes.Proof.FirstEnd) (file : ByteArray) (s : Session) {N1 N2 N3 : Nat}
    (h1 : FirstBelow cs table copy request words block N1)
    (h2 : SharedBelow (OnBytes.Proof.tailPublic cs table) N2)
    (h3 : ∀ x first, block.dryRun (OnBytes.Proof.firstStart cs.first) = some x →
      SecondBelow (OnBytes.Proof.tailPublic cs table) x.2 first N3) :
    (M.Proof.readProof (Fmt.HM askB) cs table copy request words block file s).run.NoCoin ∧
      (M.Proof.readProof (Fmt.HM askB) cs table copy request words block file s).run.QueryBound
        ((2 * N1 + tailN (OnBytes.Proof.tailPublic cs table) N2 N3) * 2) :=
  have e := leR_readProof (qp 256) 2 (Fmt.HM askB) qp_HM cs table copy request words block file h1
    h2 h3 s
  ⟨e.1, e.2.1⟩

/-- The reading of a key file that asks the one oracle. -/
theorem readKey_asks (ks : KeyChains) (table : TableName) (file : ByteArray) (j : Nat) (s : Session)
    {N1 N2 N3 : Nat} (h1 : OneTimeBelow ks table N1)
    (h2 : SharedBelow (OnBytes.Key.tailPublic ks table) N2)
    (h3 : ∀ x first, (OnBytes.Key.oneTime ks.oneTime).dryRun (OnBytes.Key.startOf ks.oneTime) =
        some x → SecondBelow (OnBytes.Key.tailPublic ks table) x.2 first N3) :
    (M.Key.readKey (Fmt.HM askB) ks table file j s).run.NoCoin ∧
      (M.Key.readKey (Fmt.HM askB) ks table file j s).run.QueryBound
        ((2 * N1 + tailN (OnBytes.Key.tailPublic ks table) N2 N3) * 2) :=
  have e := leR_readKey (qp 256) 2 (Fmt.HM askB) qp_HM ks table file j h1 h2 h3 s
  ⟨e.1, e.2.1⟩

/-- The reading of an entry file that asks the one oracle: no coin, and at most
(2 · the key's number + 2 · N) · 2 strings, N a bound on the number of every description that the
reading can make. -/
theorem entryRead_asks (p : Params.Link) (first : TableName) (file : ByteArray) (N : Nat)
    (hN : RoadCost.SpecsBelow p first N) :
    (M.Entry.read (Fmt.HM askB) p first file).NoCoin ∧
      (M.Entry.read (Fmt.HM askB) p first file).QueryBound
        ((2 * RoadCost.keyN p.link.table + 2 * N) * 2) :=
  have e := RoadCost.le_read (qp 256) 2 (Fmt.HM askB) qp_HM p first file N hN
  ⟨e.1, e.2.1⟩

/-- The same under the hypothesis that speaks of fitting keys alone. -/
theorem entryRead_asksFit (p : Params.Link) (first : TableName) (file : ByteArray) (N : Nat)
    (hN : SpecsBelowFit p first N) :
    (M.Entry.read (Fmt.HM askB) p first file).NoCoin ∧
      (M.Entry.read (Fmt.HM askB) p first file).QueryBound
        ((2 * RoadCost.keyN p.link.table + 2 * N) * 2) :=
  have e := le_readFit (qp 256) 2 (Fmt.HM askB) qp_HM p first file N hN
  ⟨e.1, e.2.1⟩

end OnBytes.TwoPort.M.AsksLands
