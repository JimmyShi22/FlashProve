-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/RecWholeProof.lean: honest-verifier zero knowledge of the whole object with records.

Proofs of `Spec.rec_hvzk_whole` and `Spec.rec_hvzk_whole_hiding` of Hiop/RecWhole.lean.

As Hiop/WholeProof.lean: replace each run by its simulator, which still reads the true encodings;
then see environment and simulators as one algorithm that reads a table with independent rows. New:
a row also holds the record of its encoded index, at a free place (Hiop/RecWholeKit.lean; word
places: `Free.wp`): the record is shown to the environment and handed to the simulators of runs, so
everybody reads it, as often as they like, and it costs nothing. That rests on the object's
own clause (`ReadsR.hidE`, in `L.ReadsR b qT qpar qch qon`: a premise): the law of (honest answer,
any b positions) does not depend on the index, at every seed.
 Part 1: the real side and the simulator of the theorem are the same host for two families of laws
   (`LawsR`, `LawsR.host`);
 Part 2: the game with all randomness drawn at the start; "show the record" is a call of its own
   (`RCall`); the environment as an adversary of that game (`toPlayR`, `wholeR`);
 Part 3: for an environment within its bounds, drawing when asked is drawing at the start
   (`runR_eq`, `viewR_eq`);
 Part 4: the row law (`row_law`: `ReadsR.hidE` averaged over the seed); the simulated runs as
   readers of the table (`simRR`), their loads; the lifetime theorem (`lifetimeR`, by `lifetimeD`,
   Hiop/RecWholeKit.lean);
 Part 5: an environment within its bounds makes allowed calls, keeps every encoded index within the
   budget (given `InvR`), and its errors add up to at most the error of the statement.

Limits: see the header of Hiop/RecWhole.lean.
Terms: lean/GLOSSARY.md.
-/
import Hiop.RecWhole
import Hiop.RecWholeKit
import Hiop.WholeProof

set_option autoImplicit false

noncomputable section

namespace Hiop
open Prob Iop Compile.Lifetime Compile.BatchLife Hiop.Free
open scoped ENNReal

variable {I X : Type} {L : HolographicProtocol I X} {α : Type}

/-! ## Part 1. One host for two families of laws -/

/-- The record, the laws of what is shown of the three kinds of runs, and the symbols of an encoded
index, as functions of (committer's randomness, seed). -/
structure LawsR (L : HolographicProtocol I X) where
  rc : L.EncodingRandomness × L.OutOfDomainSeed → L.Rec
  T : L.EncodingRandomness × L.OutOfDomainSeed → PMF (Sess L.offline)
  Lk : L.EncodingRandomness × L.OutOfDomainSeed → L.EncodingRandomness × L.OutOfDomainSeed → PMF (Sess L.link)
  B : L.EncodingRandomness × L.OutOfDomainSeed → (J : Finset (Fin L.maxBatchSize)) → (J → X) →
    ({j : Fin L.maxBatchSize // j ∉ J} → Option X) → PMF (BSess L.onlineBatch J)
  y : L.EncodingRandomness × L.OutOfDomainSeed → Fin L.wordLength → L.Symbol

def LawsR.host (W : LawsR L) : HostR L where
  σ := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)
  start := (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u => (W.rc u, (0, fun _ => u))
  fresh := fun s =>
    (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u => (W.rc u, (s.1 + 1, Function.update s.2 (s.1 + 1) u))
  test := fun s e => (W.T (s.2 e)).map fun a => (a, s)
  link := fun s e => (W.Lk (s.2 0) (s.2 e)).map fun a => (a, s)
  session := fun s e J xs rest => (W.B (s.2 e) J xs rest).map fun a => (a, s)
  read := fun s e p => PMF.pure (W.y (s.2 e) p, s)

def realLawsR (L : HolographicProtocol I X) (i : I) : LawsR L where
  rc := fun u => L.recOf i u.1 u.2
  T := fun u => sess L.honestOfflineProver (i, u.1, u.2) (L.recOf i u.1 u.2)
  Lk := fun u u' => sess L.honestLinkProver (i, u, u') (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2)
  B := fun u J xs rest =>
    bsess L.honestOnlineBatchProver (i, u.1, u.2)
      (vec J (fun j => (xs j, L.recOf i u.1 u.2))
        (fun j => (rest j).map fun x => (x, L.recOf i u.1 u.2))) J
  y := fun u p => L.encodeIndex i u.1 p

def simLawsR (L : HolographicProtocol I X) (Sm : SimsR L) (i₀ : I) : LawsR L where
  rc := fun u => L.recOf i₀ u.1 u.2
  T := fun u => simSess L.offline Sm.T (L.recOf i₀ u.1 u.2) (L.encodeIndex i₀ u.1)
  Lk := fun u u' =>
    simSess L.link Sm.Lk (L.recOf i₀ u.1 u.2, L.recOf i₀ u'.1 u'.2) (L.encodeIndex i₀ u.1, L.encodeIndex i₀ u'.1)
  B := fun u J xs _ => simBsess L.onlineBatch Sm.B J (fun j => (xs j, L.recOf i₀ u.1 u.2)) (L.encodeIndex i₀ u.1)
  y := fun u p => L.encodeIndex i₀ u.1 p

theorem realHostR_eq (i : I) : realHostR L i = (realLawsR L i).host := rfl
theorem simHostR_eq (Sm : SimsR L) (i₀ : I) : (simWholeR L Sm i₀).host = (simLawsR L Sm i₀).host :=
  rfl

section HostEqs
variable (W : LawsR L)
abbrev StR (L : HolographicProtocol I X) : Type := ℕ × (ℕ → L.EncodingRandomness × L.OutOfDomainSeed)

theorem viewR_host (E : L.Rec → EnvR L α) :
    W.host.view E =
      (unif (L.EncodingRandomness × L.OutOfDomainSeed)).bind fun u => (E (W.rc u)).run W.host (0, fun _ => u) := by
  show ((unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u => (W.rc u, ((0, fun _ => u) : StR L))).bind
      (fun p => (E p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runR_stop (a : α) (s : StR L) : (EnvR.stop a : EnvR L α).run W.host s = PMF.pure a := rfl
theorem runR_draw (β : Type) (d : PMF β) (k : β → EnvR L α) (s : StR L) :
    (EnvR.draw β d k).run W.host s = d.bind fun y => (k y).run W.host s := rfl
theorem runR_fresh (k : L.Rec → EnvR L α) (c : ℕ) (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) :
    (EnvR.fresh k).run W.host (c, f) =
      (unif (L.EncodingRandomness × L.OutOfDomainSeed)).bind fun u =>
        (k (W.rc u)).run W.host (c + 1, Function.update f (c + 1) u) := by
  show ((unif (L.EncodingRandomness × L.OutOfDomainSeed)).map fun u =>
        (W.rc u, ((c + 1, Function.update f (c + 1) u) : StR L))).bind
      (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runR_test (e : ℕ) (k : Sess L.offline → EnvR L α) (s : StR L) :
    (EnvR.test e k).run W.host s = (W.T (s.2 e)).bind fun a => (k a).run W.host s := by
  show ((W.T (s.2 e)).map fun a => (a, s)).bind (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runR_link (e : ℕ) (k : Sess L.link → EnvR L α) (s : StR L) :
    (EnvR.link e k).run W.host s = (W.Lk (s.2 0) (s.2 e)).bind fun a => (k a).run W.host s := by
  show ((W.Lk (s.2 0) (s.2 e)).map fun a => (a, s)).bind (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runR_session (e : ℕ) (J : Finset (Fin L.maxBatchSize)) (xs : J → X)
    (rest : {j : Fin L.maxBatchSize // j ∉ J} → Option X) (k : BSess L.onlineBatch J → EnvR L α) (s : StR L) :
    (EnvR.session e J xs rest k).run W.host s =
      (W.B (s.2 e) J xs rest).bind fun a => (k a).run W.host s := by
  show ((W.B (s.2 e) J xs rest).map fun a => (a, s)).bind (fun p => (k p.1).run W.host p.2) = _
  simp only [PMF.bind_map, Function.comp_def]
theorem runR_read (e : ℕ) (p : Fin L.wordLength) (k : L.Symbol → EnvR L α) (s : StR L) :
    (EnvR.read e p k).run W.host s = (k (W.y (s.2 e) p)).run W.host s := by
  show (PMF.pure (W.y (s.2 e) p, s)).bind (fun q => (k q.1).run W.host q.2) = _
  rw [PMF.pure_bind]
end HostEqs

/-! ## Part 2. The game with all randomness drawn at the start -/

/-- The calls. -/
inductive RCall (ι X : Type) (N n : ℕ) : Type
  /-- show the record of the encoded index e -/
  | rcd (e : ι) : RCall ι X N n
  | test (e : ι) : RCall ι X N n
  | link (e e' : ι) : RCall ι X N n
  | bat (e : ι) (J : Finset (Fin N)) (xs : J → X) (rest : {j : Fin N // j ∉ J} → Option X) : RCall ι X N n
  | read (e : ι) (p : Fin n) : RCall ι X N n

def RAns (L : HolographicProtocol I X) {ι : Type} : RCall ι X L.maxBatchSize L.wordLength → Type
  | .rcd _ => L.Rec
  | .test _ => Sess L.offline
  | .link _ _ => Sess L.link
  | .bat _ J _ _ => BSess L.onlineBatch J
  | .read _ _ => L.Symbol

def LawsR.O (W : LawsR L) {ι : Type} (r : ι → L.EncodingRandomness × L.OutOfDomainSeed) :
    ∀ c : RCall ι X L.maxBatchSize L.wordLength, PMF (RAns L c)
  | .rcd e => PMF.pure (W.rc (r e))
  | .test e => W.T (r e)
  | .link e e' => W.Lk (r e) (r e')
  | .bat e J xs rest => W.B (r e) J xs rest
  | .read e p => PMF.pure (W.y (r e) p)

/-- The environment, when c further encoded indices exist, as an adversary of that game. -/
def toPlayR (M : ℕ) : EnvR L α → ℕ → Play (RCall (Fin (M + 1)) X L.maxBatchSize L.wordLength) (RAns L) α
  | .stop a, _ => .done a
  | .fresh k, c => .call (.rcd (nm M (c + 1))) fun (a : L.Rec) => toPlayR M (k a) (c + 1)
  | .test e k, c => .call (.test (nm M e)) fun (a : Sess L.offline) => toPlayR M (k a) c
  | .link e k, c => .call (.link (nm M 0) (nm M e)) fun (a : Sess L.link) => toPlayR M (k a) c
  | .session e J xs rest k, c => .call (.bat (nm M e) J xs rest) fun (a : BSess L.onlineBatch J) => toPlayR M (k a) c
  | .read e p k, c => .call (.read (nm M e) p) fun (y : L.Symbol) => toPlayR M (k y) c
  | .draw β d k, c => .draw β d fun y => toPlayR M (k y) c

/-- With the first record in front. -/
def wholeR (M : ℕ) (E : L.Rec → EnvR L α) : Play (RCall (Fin (M + 1)) X L.maxBatchSize L.wordLength) (RAns L) α :=
  .call (.rcd (nm M 0)) fun (a : L.Rec) => toPlayR M (E a) 0

/-! ## Part 3. Drawing when asked is drawing at the start -/

theorem runR_eq (W : LawsR L) {B : BoundsR} {ok : X → Prop} (t : EnvR L α) :
    ∀ (c : ℕ) (f : ℕ → L.EncodingRandomness × L.OutOfDomainSeed) (u : UsedR), t.Adm B ok c u → c ≤ B.nenc →
      t.run W.host (c, f) =
        (unif (Fin (B.nenc + 1) → L.EncodingRandomness × L.OutOfDomainSeed)).bind fun tab =>
          (toPlayR B.nenc t c).run (W.O (merge c f tab)) := by
  induction t with
  | stop a =>
    intro c f u _ _
    simp only [runR_stop, toPlayR, Play.run_done, PMF.bind_const]
  | draw β d k ih =>
    intro c f u h hc
    simp only [runR_draw, toPlayR, Play.run_draw]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun y => ih y c f u (h y) hc)
  | test e k ih =>
    intro c f u h hc
    obtain ⟨he, -, h3⟩ := h
    simp only [runR_test, toPlayR, Play.run_call, LawsR.O, merge_nm f _ he hc]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a c f _ (h3 a) hc)
  | link e k ih =>
    intro c f u h hc
    obtain ⟨-, he, -, h3⟩ := h
    simp only [runR_link, toPlayR, Play.run_call, LawsR.O,
      merge_nm f _ he hc, merge_nm f _ (Nat.zero_le c) hc]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a c f _ (h3 a) hc)
  | session e J xs rest k ih =>
    intro c f u h hc
    obtain ⟨he, -, -, -, -, h6⟩ := h
    simp only [runR_session, toPlayR, Play.run_call, LawsR.O, merge_nm f _ he hc]
    rw [Prob.bind_comm]
    exact congrArg _ (funext fun a => ih a c f _ (h6 a) hc)
  | read e p k ih =>
    intro c f u h hc
    obtain ⟨he, -, h3⟩ := h
    simp only [runR_read, toPlayR, Play.run_call, LawsR.O, merge_nm f _ he hc, PMF.pure_bind]
    exact ih _ c f _ (h3 _) hc
  | fresh k ih =>
    intro c f u h hc
    obtain ⟨hlt, h2⟩ := h
    simp only [runR_fresh, toPlayR, Play.run_call, LawsR.O, PMF.pure_bind]
    rw [← unif_resample (nm B.nenc (c + 1))]
    refine congrArg _ (funext fun r => ?_)
    have h1 : ∀ tab : Fin (B.nenc + 1) → L.EncodingRandomness × L.OutOfDomainSeed,
        merge (c + 1) (Function.update f (c + 1) r) tab (nm B.nenc (c + 1)) = r := fun tab => by
      rw [merge_nm _ _ le_rfl hlt, Function.update_self]
    simp only [merge_update f _ r hlt, h1]
    exact ih _ (c + 1) _ u (h2 _) hlt

theorem viewR_eq (W : LawsR L) {B : BoundsR} {ok : X → Prop} {u : UsedR}
    (E : L.Rec → EnvR L α) (hE : ∀ a, (E a).Adm B ok 0 u) :
    W.host.view E =
      (unif (Fin (B.nenc + 1) → L.EncodingRandomness × L.OutOfDomainSeed)).bind fun tab =>
        (wholeR B.nenc E).run (W.O tab) := by
  unfold wholeR
  simp only [viewR_host, Play.run_call, LawsR.O, PMF.pure_bind]
  rw [← unif_resample (nm B.nenc 0)]
  refine congrArg _ (funext fun r => ?_)
  simp only [merge_zero, merge_nm (fun _ => r) _ le_rfl (Nat.zero_le B.nenc)]
  exact runR_eq W (E _) 0 _ u (hE _) (Nat.zero_le _)


/-! ## Part 4. The row law, the simulated runs as readers, the lifetime theorem -/

/-- Under the hypotheses below, the law of (record, any b positions) of an encoded index with a
uniform seed does not depend on the index: `ReadsR.hidE`, averaged over the seed. -/
theorem row_law {b qT qpar qch qon : ℕ} (hR : L.ReadsR b qT qpar qch qon) (T : Finset (Fin L.wordLength))
    (hT : T.card ≤ b) (i i₀ : I) :
    (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map (fun u => (L.recOf i u.1 u.2, fun p : T => L.encodeIndex i u.1 p)) =
      (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map (fun u => (L.recOf i₀ u.1 u.2, fun p : T => L.encodeIndex i₀ u.1 p)) := by
  have key : ∀ j : I,
      (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map (fun u => (L.recOf j u.1 u.2, fun p : T => L.encodeIndex j u.1 p)) =
        (unif L.OutOfDomainSeed).bind fun s =>
          ((unif L.EncodingRandomness).map fun r => (L.honestOutOfDomainAnswer j r s, fun p : T => L.encodeIndex j r p)).map
              fun aw => (((s, aw.1) : L.Rec), aw.2) := by
    intro j
    calc
      (unif (L.EncodingRandomness × L.OutOfDomainSeed)).map (fun u => (L.recOf j u.1 u.2, fun p : T => L.encodeIndex j u.1 p)) =
          (Prob.prod (unif L.EncodingRandomness) (unif L.OutOfDomainSeed)).bind fun u =>
            PMF.pure (L.recOf j u.1 u.2, fun p : T => L.encodeIndex j u.1 p) := by
          rw [unif_prod]
          rfl
      _ = (unif L.EncodingRandomness).bind fun r =>
            (unif L.OutOfDomainSeed).bind fun s => PMF.pure (L.recOf j r s, fun p : T => L.encodeIndex j r p) :=
          (bind_bind_eq_prod_bind _ _ fun r s =>
            PMF.pure (L.recOf j r s, fun p : T => L.encodeIndex j r p)).symm
      _ = (unif L.OutOfDomainSeed).bind fun s =>
            (unif L.EncodingRandomness).bind fun r => PMF.pure (L.recOf j r s, fun p : T => L.encodeIndex j r p) :=
        Prob.bind_comm _ _ _
      _ = _ := congrArg _ (funext fun s => by
          rw [PMF.map_comp]
          rfl)
  rw [key i, key i₀]
  exact congrArg _ (funext fun s => by rw [hR.hidE T hT s i i₀])

section Life
variable {ι : Type}

def okR (ok : X → Prop) {N n : ℕ} : RCall ι X N n → Prop
  | .bat _ _ xs rest => (∀ j, ok (xs j)) ∧ ∀ j x, rest j = some x → ok x
  | _ => True

def errR (zT zL zO : ℝ≥0∞) {N n : ℕ} : RCall ι X N n → ℝ≥0∞
  | .test _ => zT
  | .link _ _ => zL
  | .bat _ J _ _ => J.card * zO
  | _ => 0

/-- the word places that a call may read in row a. The record costs nothing. -/
def loadR [DecidableEq ι] (qT qpar qch qon : ℕ) {N n : ℕ} : RCall ι X N n → ι → ℕ
  | .rcd _, _ => 0
  | .test e, a => if a = e then qT else 0
  | .link e e', a => (if a = e then qpar else 0) + if a = e' then qch else 0
  | .bat e _ _ _, a => if a = e then qon else 0
  | .read e _, a => if a = e then 1 else 0

/-- the table: row e holds the record of the encoded index e at its free place, and the encoded
index -/
def tabR (L : HolographicProtocol I X) (j : I) (r : ι → L.EncodingRandomness × L.OutOfDomainSeed) : ∀ p, Sy ι (Fin L.wordLength) L.Rec L.Symbol p :=
  Free.tab (fun e => L.recOf j (r e).1 (r e).2) fun e => L.encodeIndex j (r e).1

/-- The simulated runs as algorithms that read the table: first the record(s), at the free place(s);
then as in Compile/Batch/Life.lean. -/
def simRR (L : HolographicProtocol I X) (Sm : SimsR L) :
    ∀ c : RCall ι X L.maxBatchSize L.wordLength, Reader (ι × Option (Fin L.wordLength)) (Sy ι (Fin L.wordLength) L.Rec L.Symbol) (RAns L c)
  | .rcd e => .read (e, none) fun (a : L.Rec) => .done a
  | .test e => .read (e, none) fun (a : L.Rec) => up (sessR L.offline Sm.T a fun p => (e, p))
  | .link e e' => .read (e, none) fun (a : L.Rec) => .read (e', none) fun (a' : L.Rec) =>
      up (sessR L.link Sm.Lk (a, a') (Sum.elim (fun p => (e, p)) fun p => (e', p)))
  | .bat e J xs _ =>
    .read (e, none) fun (a : L.Rec) => up (bsessR L.onlineBatch Sm.B J (fun j => (xs j, a)) fun p => (e, p))
  | .read e p => up (.read (e, p) fun y => .done y)

theorem run_simRR (Sm : SimsR L) (j : I) (r : ι → L.EncodingRandomness × L.OutOfDomainSeed) (c : RCall ι X L.maxBatchSize L.wordLength) :
    (simRR L Sm c).run (tabR L j r) = (simLawsR L Sm j).O r c := by
  cases c with
  | rcd e => rfl
  | test e =>
    show (up (sessR L.offline Sm.T (L.recOf j (r e).1 (r e).2) fun p => (e, p))).run (tabR L j r) = _
    rw [run_up]
    exact run_sessR L.offline Sm.T _ _ _ (L.encodeIndex j (r e).1) fun _ => rfl
  | link e e' =>
    show (up (sessR L.link Sm.Lk (L.recOf j (r e).1 (r e).2, L.recOf j (r e').1 (r e').2)
            (Sum.elim (fun p => (e, p)) fun p => (e', p)))).run (tabR L j r) = _
    rw [run_up]
    exact run_sessR L.link Sm.Lk _ _ _ (L.encodeIndex j (r e).1, L.encodeIndex j (r e').1) fun q => by
      cases q <;> rfl
  | bat e J xs rest =>
    show (up (bsessR L.onlineBatch Sm.B J (fun k => (xs k, L.recOf j (r e).1 (r e).2)) fun p => (e, p))).run
        (tabR L j r) = _
    rw [run_up]
    exact run_bsessR Sm.B J _ _ _ (L.encodeIndex j (r e).1) fun _ => rfl
  | read e p => rfl

variable [DecidableEq ι]

theorem adds_simRR {b qT qpar qch qon : ℕ} (hR : L.ReadsR b qT qpar qch qon)
    (Sm : SimsR L) (c : RCall ι X L.maxBatchSize L.wordLength) :
    AddsF (simRR L Sm c) (loadR qT qpar qch qon c) := by
  cases c with
  | rcd e =>
    intro S x a
    show rowCard (wp (insert (e, none) S)) a ≤ rowCard (wp S) a + 0
    rw [wp_insert_free]
    exact le_rfl
  | test e =>
    exact addsF_free e fun x =>
      addsF_up fun S =>
        within_sessR L.offline Sm.T x _ S fun ρ a =>
          (rowCard_union_image_le S _ _ a).trans
            (Nat.add_le_add_left (card_filter_const_le _ e a (hR.cntT x ρ)) _)
  | bat e J xs rest =>
    exact addsF_free e fun x =>
      addsF_up fun S =>
        within_bsessR Sm.B J _ _ S fun ρ a =>
          (rowCard_union_image_le S _ _ a).trans
            (Nat.add_le_add_left (card_filter_const_le _ e a (card_readsJ_le hR.cntB J _ ρ)) _)
  | link e e' =>
    refine addsF_free e fun x =>
        addsF_free e' fun x' => addsF_up fun S => within_sessR L.link Sm.Lk (x, x') _ S fun ρ a =>
      (rowCard_union_image_le S _ _ a).trans (Nat.add_le_add_left ?_ _)
    have hsub : ((L.link.extReads (x, x') ρ).filter fun q =>
          ((Sum.elim (fun p => (e, p)) fun p => (e', p) : Fin L.wordLength ⊕ Fin L.wordLength → ι × Fin L.wordLength) q).1 = a)
        ⊆ (((L.link.extReads (x, x') ρ).filter fun p => p.isLeft).filter fun _ => e = a)
          ∪ (((L.link.extReads (x, x') ρ).filter fun p => p.isRight).filter fun _ => e' = a) := by
      intro q hq
      obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
      cases q with
      | inl p =>
        exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hq1, rfl⟩, hq2⟩)
      | inr p =>
        exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hq1, rfl⟩, hq2⟩)
    exact (Finset.card_le_card hsub).trans
      ((Finset.card_union_le _ _).trans
        (Nat.add_le_add (card_filter_const_le _ e a (hR.cntLp (x, x') ρ))
          (card_filter_const_le _ e' a (hR.cntLc (x, x') ρ))))
  | read e p =>
    refine addsF_up fun S y a => ?_
    show rowCard (insert (e, p) S) a ≤ rowCard S a + if a = e then 1 else 0
    unfold rowCard
    by_cases h : a = e
    · rw [if_pos h, Finset.filter_insert]
      split_ifs
      · exact Finset.card_insert_le _ _
      · exact Nat.le_succ _
    · rw [if_neg h, Finset.filter_insert, if_neg (fun hh : e = a => h hh.symm)]
      exact le_rfl

variable [Fintype ι]

/-- Under the hypotheses below, the law of the table on a set of places with at most b word places
in each row does not depend on the index. -/
theorem table_law {b qT qpar qch qon : ℕ} (hR : L.ReadsR b qT qpar qch qon) (i i₀ : I)
    (S : Finset (ι × Option (Fin L.wordLength))) (hS : ∀ e, rowCard (wp S) e ≤ b) :
    ((unif (ι → L.EncodingRandomness × L.OutOfDomainSeed)).map fun r => tabR L i r).map (res S) =
      ((unif (ι → L.EncodingRandomness × L.OutOfDomainSeed)).map fun r => tabR L i₀ r).map (res S) :=
  rows_lawF (ι := ι) (Q := Fin L.wordLength) (F := L.Rec) (Sg := L.Symbol) (R := L.EncodingRandomness × L.OutOfDomainSeed)
    (fun _ u => L.recOf i u.1 u.2) (fun _ u => L.recOf i₀ u.1 u.2) (fun _ u => L.encodeIndex i u.1)
    (fun _ u => L.encodeIndex i₀ u.1) b (fun _ T hT => row_law hR T hT i i₀) S hS

/-- What the theorem needs of the real side: its records and symbols are those of the encodings of
i, and each of its runs is near the simulated run on the true encodings and records, for every value
of (committer's randomness, seed) (the field `B`: under `(∀ j, ok (xs j))` and
`(∀ j x, rest j = some x → ok x)`). -/
structure LawsR.Near (W : LawsR L) (Sm : SimsR L) (i : I) (ok : X → Prop) (zT zL zO : ℝ≥0∞) :
    Prop where
  rc : ∀ u, W.rc u = L.recOf i u.1 u.2
  y  : ∀ u p, W.y u p = L.encodeIndex i u.1 p
  T  : ∀ u, tv (W.T u) (simSess L.offline Sm.T (L.recOf i u.1 u.2) (L.encodeIndex i u.1)) ≤ zT
  Lk : ∀ u u',
    tv (W.Lk u u')
        (simSess L.link Sm.Lk (L.recOf i u.1 u.2, L.recOf i u'.1 u'.2)
          (L.encodeIndex i u.1, L.encodeIndex i u'.1)) ≤ zL
  B  : ∀ u J xs rest, (∀ j, ok (xs j)) → (∀ j x, rest j = some x → ok x) →
    tv (W.B u J xs rest)
        (simBsess L.onlineBatch Sm.B J (fun j => (xs j, L.recOf i u.1 u.2)) (L.encodeIndex i u.1)) ≤ J.card * zO

theorem lifetimeR {ok : X → Prop} {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞}
    (hR : L.ReadsR b qT qpar qch qon) {Sm : SimsR L} {W : LawsR L} {i : I}
    (hN : W.Near Sm i ok zT zL zO) (i₀ : I) (t : Play (RCall ι X L.maxBatchSize L.wordLength) (RAns L) α)
    (hok : t.Calls (okR ok)) (hfit : t.Fits (loadR qT qpar qch qon) b fun _ => 0) :
    tv ((unif (ι → L.EncodingRandomness × L.OutOfDomainSeed)).bind fun r => t.run (W.O r))
        ((unif (ι → L.EncodingRandomness × L.OutOfDomainSeed)).bind fun r => t.run ((simLawsR L Sm i₀).O r)) ≤
      t.cost (errR zT zL zO) := by
  have h := lifetimeD (unif (ι → L.EncodingRandomness × L.OutOfDomainSeed)) (fun r => tabR L i r)
    ((unif (ι → L.EncodingRandomness × L.OutOfDomainSeed)).map fun r => tabR L i₀ r) (fun r => W.O r) (simRR L Sm) (okR ok)
    (errR zT zL zO) (fun T => ∀ e, rowCard (wp T) e ≤ b) ?_ ?_ t hok ?_
  · rw [PMF.bind_map] at h
    have e1 : ∀ r : ι → L.EncodingRandomness × L.OutOfDomainSeed,
        (t.run fun c => (simRR L Sm c).run (tabR L i₀ r)) = t.run ((simLawsR L Sm i₀).O r) :=
      fun r => congrArg t.run (funext fun c => run_simRR Sm i₀ r c)
    simp only [← e1]
    exact h
  · intro r c hc
    rw [run_simRR Sm i r c]
    cases c with
    | rcd e =>
      show tv (PMF.pure (W.rc (r e))) (PMF.pure (L.recOf i (r e).1 (r e).2)) ≤ 0
      rw [hN.rc, tv_self]
    | test e => exact hN.T (r e)
    | link e e' => exact hN.Lk (r e) (r e')
    | bat e J xs rest => exact hN.B (r e) J xs rest hc.1 hc.2
    | read e p =>
      show tv (PMF.pure (W.y (r e) p)) (PMF.pure (L.encodeIndex i (r e).1 p)) ≤ 0
      rw [hN.y, tv_self]
  · exact fun S hSb => table_law hR i i₀ S hSb
  · exact within_plugF (adds_simRR hR Sm) t (fun _ => 0) ∅
      (fun e => by rw [wp_empty, rowCard_empty]) hfit

/-- Under the hypotheses below, the real side of Hiop/RecWhole.lean is near good simulators. -/
theorem near_realR {Ryes : I → X → Prop} {zT zL zO : ℝ≥0∞} (hW : L.WiredR) {Sm : SimsR L}
    (hS : Sm.Good Ryes zT zL zO) (i : I) :
    (realLawsR L i).Near Sm i (Ryes i) zT zL zO where
  rc := fun _ => rfl
  y := fun _ _ => rfl
  T := fun u => by
    have h1 := tv_sess_le L.honestOfflineProver Sm.T (i, u.1, u.2) (L.recOf i u.1 u.2) (hS.goodT (i, u.1, u.2) _ rfl)
    rw [hW.extT] at h1
    exact h1
  Lk := fun u u' => by
    obtain ⟨r, s⟩ := u
    obtain ⟨r', s'⟩ := u'
    have h1 := tv_sess_le L.honestLinkProver Sm.Lk (i, (r, s), (r', s'))
      (L.recOf i r s, L.recOf i r' s') (hS.goodL (i, (r, s), (r', s')) _ rfl)
    rw [hW.extL] at h1
    exact h1
  B := fun u J xs rest h1 h2 => by
    have hv : ∀ j xj,
        vec J (fun j => (xs j, L.recOf i u.1 u.2))
            (fun j => (rest j).map fun x => (x, L.recOf i u.1 u.2)) j = some xj →
        L.validB Ryes (i, u.1, u.2) xj :=
      valid_vec J _ _ (fun j => ⟨rfl, h1 j⟩) fun j x hx => by
        cases hr : rest j with
        | none => rw [hr] at hx; cases hx
        | some x' =>
          rw [hr] at hx
          cases hx
          exact ⟨rfl, h2 j x' hr⟩
    have h3 := tv_bsess_le L.honestOnlineBatchProver Sm.B (i, u.1, u.2) _ J (fun j => (xs j, L.recOf i u.1 u.2))
      (hS.goodB (i, u.1, u.2) _ hv J _ (vec_of_mem J _ _))
    rw [hW.extB] at h3
    exact h3

end Life

/-! ## Part 5. An environment within its bounds -/

section Nice
variable {B : BoundsR} {ok : X → Prop}

theorem calls_toPlayR (t : EnvR L α) :
    ∀ (c : ℕ) (u : UsedR), t.Adm B ok c u → (toPlayR B.nenc t c).Calls (okR ok) := by
  induction t with
  | stop a => intro c u _; exact trivial
  | draw β d k ih => intro c u h; exact fun y => ih y c u (h y)
  | fresh k ih => intro c u h; exact ⟨trivial, fun a => ih a (c + 1) u (h.2 a)⟩
  | test e k ih => intro c u h; exact ⟨trivial, fun a => ih a c _ (h.2.2 a)⟩
  | link e k ih => intro c u h; exact ⟨trivial, fun a => ih a c _ (h.2.2.2 a)⟩
  | session e J xs rest k ih => intro c u h; exact ⟨⟨h.2.2.2.1, h.2.2.2.2.1⟩, fun a => ih a c _ (h.2.2.2.2.2 a)⟩
  | read e p k ih => intro c u h; exact ⟨trivial, fun y => ih y c _ (h.2.2 y)⟩

/-- What may still be asked for, summed over the encoded indices. -/
def leftR (B : BoundsR) (f u : ℕ → ℕ) : ℕ := ∑ j ∈ Finset.range (B.nenc + 1), (f j - u j)

theorem leftR_step {f u : ℕ → ℕ} {e : ℕ} (he : e ≤ B.nenc) (h : u e < f e) :
    leftR B f u = leftR B f (bump u e) + 1 := by
  have hmem : e ∈ Finset.range (B.nenc + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le he)
  unfold leftR bump
  rw [← Finset.add_sum_erase _ (fun j => f j - u j) hmem,
    ← Finset.add_sum_erase _ (fun j => f j - Function.update u e (u e + 1) j) hmem]
  have h1 : ∑ j ∈ (Finset.range (B.nenc + 1)).erase e, (f j - Function.update u e (u e + 1) j)
      = ∑ j ∈ (Finset.range (B.nenc + 1)).erase e, (f j - u j) :=
    Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [h1]
  simp only [Function.update_self]
  omega

theorem bump_self (u : ℕ → ℕ) (e : ℕ) : bump u e e = u e + 1 := Function.update_self _ _ _
theorem bump_ne (u : ℕ → ℕ) {e j : ℕ} (h : j ≠ e) : bump u e j = u j := Function.update_of_ne h _ _

theorem sub_step {a u : ℕ} (q : ℕ) (h : u < a) : (a - u) * q = (a - (u + 1)) * q + q := by
  have : a - u = (a - (u + 1)) + 1 := by omega
  rw [this, Nat.add_mul, Nat.one_mul]

/-- What the encoded index j may still be asked for fits beside the load that it carries. -/
def InvR (B : BoundsR) (b qT qpar qch qon : ℕ) (u : UsedR) (ld : Fin (B.nenc + 1) → ℕ) : Prop :=
  ∀ j, j ≤ B.nenc →
    ld (nm B.nenc j) + (B.tests j - u.tests j) * qT +
        (if j = 0 then leftR B B.links u.links * qpar else 0) + (B.links j - u.links j) * qch +
        (B.sess j - u.sess j) * qon + (B.reads j - u.reads j) ≤ b

theorem fits_toPlayR {b qT qpar qch qon : ℕ} (t : EnvR L α) :
    ∀ (c : ℕ) (u : UsedR) (ld : Fin (B.nenc + 1) → ℕ), t.Adm B ok c u → c ≤ B.nenc →
      InvR B b qT qpar qch qon u ld → (toPlayR B.nenc t c).Fits (loadR qT qpar qch qon) b ld := by
  induction t with
  | stop a =>
    intro c u ld _ _ hI e
    have h := hI e (Nat.le_of_lt_succ e.2)
    rw [nm_coe] at h
    omega
  | draw β d k ih => intro c u ld h hc hI; exact fun y => ih y c u ld (h y) hc hI
  | fresh k ih =>
    intro c u ld h hc hI a
    exact ih a (c + 1) u _ (h.2 a) h.1 fun j hj => hI j hj
  | test e k ih =>
    intro c u ld h hc hI a
    obtain ⟨he, hs, h3⟩ := h
    refine ih a c _ _ (h3 a) hc fun j hj => ?_
    have h := hI j hj
    show ld (nm B.nenc j) + (if nm B.nenc j = nm B.nenc e then qT else 0) +
        (B.tests j - bump u.tests e j) * qT + _ + _ + _ + _ ≤ b
    dsimp only
    by_cases hje : j = e
    · subst hje
      have e1 := sub_step qT hs
      rw [if_pos rfl, bump_self]
      omega
    · rw [if_neg (fun hh => hje ((nm_inj hj (he.trans hc)).1 hh)), bump_ne _ hje]
      omega
  | link e k ih =>
    intro c u ld h hc hI a
    obtain ⟨h1e, he, hs, h3⟩ := h
    refine ih a c _ _ (h3 a) hc fun j hj => ?_
    have h := hI j hj
    have e0 : leftR B B.links u.links * qpar = leftR B B.links (bump u.links e) * qpar + qpar := by
      rw [leftR_step (he.trans hc) hs, Nat.add_mul, Nat.one_mul]
    show ld (nm B.nenc j) +
        ((if nm B.nenc j = nm B.nenc 0 then qpar else 0) +
          if nm B.nenc j = nm B.nenc e then qch else 0) +
        _ + (if j = 0 then leftR B B.links (bump u.links e) * qpar else 0) +
        (B.links j - bump u.links e j) * qch + _ + _ ≤ b
    dsimp only
    by_cases hj0 : j = 0
    · subst hj0
      have hne : (0 : ℕ) ≠ e := by omega
      rw [if_pos rfl, if_neg (fun hh => hne ((nm_inj hj (he.trans hc)).1 hh)),
        if_pos rfl, bump_ne _ hne]
      rw [if_pos rfl] at h
      omega
    · rw [if_neg (fun hh => hj0 ((nm_inj hj (Nat.zero_le _)).1 hh)), if_neg hj0]
      rw [if_neg hj0] at h
      by_cases hje : j = e
      · subst hje
        have e1 := sub_step qch hs
        rw [if_pos rfl, bump_self]
        omega
      · rw [if_neg (fun hh => hje ((nm_inj hj (he.trans hc)).1 hh)), bump_ne _ hje]
        omega
  | session e J xs rest k ih =>
    intro c u ld h hc hI a
    obtain ⟨he, hs, -, -, -, h6⟩ := h
    refine ih a c _ _ (h6 a) hc fun j hj => ?_
    have h := hI j hj
    show ld (nm B.nenc j) + (if nm B.nenc j = nm B.nenc e then qon else 0) + _ + _ + _ +
        (B.sess j - bump u.sess e j) * qon + _ ≤ b
    dsimp only
    by_cases hje : j = e
    · subst hje
      have e1 := sub_step qon hs
      rw [if_pos rfl, bump_self]
      omega
    · rw [if_neg (fun hh => hje ((nm_inj hj (he.trans hc)).1 hh)), bump_ne _ hje]
      omega
  | read e p k ih =>
    intro c u ld h hc hI y
    obtain ⟨he, hs, h3⟩ := h
    refine ih y c _ _ (h3 y) hc fun j hj => ?_
    have h := hI j hj
    show ld (nm B.nenc j) + (if nm B.nenc j = nm B.nenc e then 1 else 0) +
        _ + _ + _ + _ + (B.reads j - bump u.reads e j) ≤ b
    dsimp only
    by_cases hje : j = e
    · subst hje
      rw [if_pos rfl, bump_self]
      omega
    · rw [if_neg (fun hh => hje ((nm_inj hj (he.trans hc)).1 hh)), bump_ne _ hje]
      omega

theorem cost_toPlayR {zT zL zO : ℝ≥0∞} (t : EnvR L α) :
    ∀ (c : ℕ) (u : UsedR), t.Adm B ok c u → c ≤ B.nenc →
      (toPlayR B.nenc t c).cost (errR zT zL zO) ≤
        (leftR B B.tests u.tests : ℝ≥0∞) * zT + (leftR B B.links u.links : ℝ≥0∞) * zL +
          (leftR B B.sess u.sess : ℝ≥0∞) * (B.shown * zO) := by
  induction t with
  | stop a => intro c u _ _; exact zero_le _
  | draw β d k ih =>
    intro c u h hc
    simp only [toPlayR, Play.cost_draw]
    exact iSup_le fun y => ih y c u (h y) hc
  | fresh k ih =>
    intro c u h hc
    simp only [toPlayR, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun a => ih a (c + 1) u (h.2 a) h.1)).trans
      (le_of_eq ?_)
    show (0 : ℝ≥0∞) + _ = _
    rw [zero_add]
  | read e p k ih =>
    intro c u h hc
    simp only [toPlayR, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun y => ih y c _ (h.2.2 y) hc)).trans (le_of_eq ?_)
    show (0 : ℝ≥0∞) + _ = _
    rw [zero_add]
  | test e k ih =>
    intro c u h hc
    obtain ⟨he, hs, h3⟩ := h
    simp only [toPlayR, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun a => ih a c _ (h3 a) hc)).trans (le_of_eq ?_)
    show zT + ((leftR B B.tests (bump u.tests e) : ℝ≥0∞) * zT + _ + _) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring
  | link e k ih =>
    intro c u h hc
    obtain ⟨-, he, hs, h3⟩ := h
    simp only [toPlayR, Play.cost_call]
    refine (add_le_add (le_refl _) (iSup_le fun a => ih a c _ (h3 a) hc)).trans (le_of_eq ?_)
    show zL + (_ + (leftR B B.links (bump u.links e) : ℝ≥0∞) * zL + _) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring
  | session e J xs rest k ih =>
    intro c u h hc
    obtain ⟨he, hs, hJ, -, -, h6⟩ := h
    simp only [toPlayR, Play.cost_call]
    have h2 : errR zT zL zO (.bat (nm B.nenc e) J xs rest : RCall (Fin (B.nenc + 1)) X L.maxBatchSize L.wordLength) ≤
        B.shown * zO :=
      mul_le_mul' (Nat.cast_le.2 hJ) le_rfl
    refine (add_le_add h2 (iSup_le fun a => ih a c _ (h6 a) hc)).trans (le_of_eq ?_)
    show (B.shown : ℝ≥0∞) * zO +
        (_ + _ + (leftR B B.sess (bump u.sess e) : ℝ≥0∞) * (B.shown * zO)) = _
    rw [leftR_step (he.trans hc) hs]
    push_cast
    ring

theorem leftR_zero (B : BoundsR) (f : ℕ → ℕ) : leftR B f (fun _ => 0) = B.sum f := by
  unfold leftR BoundsR.sum
  simp only [Nat.sub_zero]

end Nice

/-! ## Part 6. The theorems -/

/-- The theorem for any real side that is near the simulated runs.
(not all hypotheses are named here: see the statement below) -/
theorem tv_viewR_le {ok : X → Prop} {b qT qpar qch qon : ℕ} {zT zL zO : ℝ≥0∞}
    (hR : L.ReadsR b qT qpar qch qon) {Sm : SimsR L} {W : LawsR L} {i : I}
    (hN : W.Near Sm i ok zT zL zO) {B : BoundsR} (hB : B.Fits b qT qpar qch qon) (i₀ : I)
    (E : L.Rec → EnvR L α) (hE : ∀ a, (E a).Adm B ok 0 UsedR.zero) :
    tv (W.host.view E) ((simWholeR L Sm i₀).host.view E) ≤ B.err zT zL zO := by
  rw [simHostR_eq, viewR_eq _ E hE, viewR_eq _ E hE]
  refine (lifetimeR hR hN i₀ (wholeR B.nenc E)
    ⟨trivial, fun a => calls_toPlayR (E a) 0 _ (hE a)⟩ ?_).trans ?_
  · intro a
    refine fits_toPlayR (E a) 0 _ _ (hE a) (Nat.zero_le _) fun j hj => ?_
    have h := hB j hj
    show 0 + 0 + (B.tests j - 0) * qT + (if j = 0 then leftR B B.links (fun _ => 0) * qpar else 0) +
        (B.links j - 0) * qch + (B.sess j - 0) * qon + (B.reads j - 0) ≤ b
    rw [leftR_zero]
    simp only [Nat.sub_zero]
    omega
  · unfold wholeR
    rw [Play.cost_call]
    refine (add_le_add (le_refl _)
        (iSup_le fun a => cost_toPlayR (E a) 0 _ (hE a) (Nat.zero_le _))).trans (le_of_eq ?_)
    show (0 : ℝ≥0∞) +
        ((leftR B B.tests (fun _ => 0) : ℝ≥0∞) * zT + (leftR B B.links (fun _ => 0) : ℝ≥0∞) * zL +
          (leftR B B.sess (fun _ => 0) : ℝ≥0∞) * (B.shown * zO)) = _
    rw [zero_add, leftR_zero, leftR_zero, leftR_zero]
    rfl

theorem rec_hvzk_whole :
    Spec.rec_hvzk_whole := fun _ _ _ _ _ _ _ _ _ _ _ _ hW hR _ hS _ hB i₀ i _ E hE =>
  tv_viewR_le hR (near_realR hW hS i) hB i₀ E hE

theorem rec_hvzk_whole_hiding : Spec.rec_hvzk_whole_hiding := by
  intro I X L Ryes b qT qpar qch qon zT zL zO hW hR hH
  obtain ⟨sT, hT⟩ := hH.hidT
  obtain ⟨sL, hL⟩ := hH.hidL
  obtain ⟨sB, hB⟩ := hH.hidB
  exact ⟨⟨sT, sL, sB⟩,
    fun B hBf i₀ =>
      rec_hvzk_whole I X L Ryes b qT qpar qch qon zT zL zO hW hR ⟨sT, sL, sB⟩ ⟨hT, hL, hB⟩ B hBf i₀⟩

end Hiop
