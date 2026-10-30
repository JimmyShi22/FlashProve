-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchSeedSame.lean: code switching: ALL TYPED OUT-OF-DOMAIN (OOD) SEEDS THAT FIT A
KEPT MEMBER's STORED SAMPLE ROWS COLLIDE ALIKE: so "no collision at the OOD seed of the held sample
as it is made" (a seed taken by choice) follows from "no collision at the OOD seed that was
sampled".

Why. The typed statement in front of the switch holds, for each kept member, an OOD sample: an OOD
seed and its OOD answers. The verifier's state stores no seed, only the sample rows made of it. So
`smpMade` (Johnson/Top/H/SwitchInXMade.lean) takes, by choice, a typed seed that fits the stored
rows. The law's condition in front also asks that no kept slot of the open word has a collision AT
THAT SEED (`KeptFree`, Johnson/Top/H0/K2Caller/PlainGood.lean). Nobody can name a chosen seed. But a
collision (`OMsg.ClashW`, Cb/Req1/LdSegKit.lean) reads a seed through its matrix alone, two seeds
that fit have the same matrix carried to the open word's entries, and at the caller of the kept
messages that carrying is one to one.
  `val_of_mat`, `clashW_of_mat`, `decW_of_mat`: seeds with one matrix have the same answers at every
  vector, collide alike, and the decoder with a sample (`OMsg.decW`) returns the same at them (by
  `pick_congr`, `decMin_of_ev`).
  `mat_of_fits`: two seeds that fit have one matrix, where the carrying is one to one.
  `smpMade_fits`: where a seed fits, the chosen one does.
  `clash_made_iff`, `dec_made_eq`: the chosen seed collides just where a given fitting seed does;
  the decoder returns the same at both.
  `push_held_inj`: at the caller of the kept messages the carrying is one to one.
  `clash_made_held`, `dec_made_held`: so there, with no premise on the carrying.
  `clash_made_sampled`: from the invariant `K2.SampleGoodS` and public facts: for each held message
  there is a seed of the program's, whose sample row is the stored one, such that the chosen seed
  collides just where that seed, typed, does.
FOR KEPT MEMBERS ALONE. The carrying is one to one because a kept member has no mask row: that is
the argument h0 of the caller of the kept messages (`heldPort`), without which its type cannot be
formed; at an entry r of the written table it is a clause of the test r.ok (`SwRow.OK.h0`,
Johnson/Top/H0/K2Caller/Row.lean). A MEMBER WITH A MASK ROW DOES NOT COME TO `KeptFree` BY THIS
ROAD. WHO PAYS `clash_made_sampled`'s PREMISES: as at `sample_made_of_goodS`:
Johnson/G/SwitchSampleTop.lean's paragraph "which premise is of which kind": a law; three tests with
code on r and the frame; one test on the front's statement and the invariant, which ride in the
law's condition in front.
Limits. That no collision stands at the sampled seed is not shown: it is for the law of the sending
that sampled it. The seed of `clash_made_sampled` stands under "there is": the invariant names a
seed whose row is stored, not the run's own draw. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H.SwitchSeedFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

/-- Seeds with one matrix have the same answers at every vector. -/
theorem val_of_mat {J : Type} [Fintype J] (Z : Cb.Ood.Sample GE J) {ρ ρ' : Z.D}
    (h : Z.mat ρ = Z.mat ρ') : Z.val ρ = Z.val ρ' := by
  funext u s
  unfold Cb.Ood.Sample.val
  rw [h]

/-- **Seeds with one matrix collide alike.** -/
theorem clashW_of_mat (o : OMsg GE) (f : o.C.Word) {ρ ρ' : o.Z.D} (h : o.Z.mat ρ = o.Z.mat ρ') :
    o.ClashW f ρ ↔ o.ClashW f ρ' := by
  unfold OMsg.ClashW Cb.Ood.Clash
  rw [val_of_mat o.Z h]

open Classical in
/-- A choice among the members of a predicate does not feel how the predicate is written. -/
theorem pick_congr {T U : Type} (view : T → U) {P P' : T → Prop} (h : P = P') :
    (if h : ∃ t, P t then some (view h.choose) else none) =
      (if h : ∃ t, P' t then some (view h.choose) else none) := by
  subst h
  rfl

/-- The decoder by a constrained minimum reads a seed through its answers alone. -/
theorem decMin_of_ev {T U D Y : Type} (dist rank : T → ℕ) (view : T → U) (ev : D → U → Y) (e : ℕ)
    {ρ ρ' : D} (h : ev ρ = ev ρ') (y : Y) :
    Cb.Ood.decMin dist rank view ev e ρ y = Cb.Ood.decMin dist rank view ev e ρ' y := by
  have hp : (fun t => Cb.Ood.First dist rank view ev ρ y t ∧ dist t ≤ e) =
      fun t => Cb.Ood.First dist rank view ev ρ' y t ∧ dist t ≤ e := by
    funext t
    unfold Cb.Ood.First
    rw [h]
  exact pick_congr view hp

/-- **At seeds with one matrix the decoder with a sample returns the same.** -/
theorem decW_of_mat (o : OMsg GE) (f : o.C.Word) {ρ ρ' : o.Z.D} (h : o.Z.mat ρ = o.Z.mat ρ')
    (y : o.Z.S → GE) : o.decW f (ρ, y) = o.decW f (ρ', y) :=
  decMin_of_ev _ _ _ _ _ (val_of_mat o.Z h) y

section General
variable {S : Sig GE} (R : RowsK S) [Nonempty R.G.P] {kp : S.O → Prop} [DecidablePred kp]
  (Hd : GHeld R.Sh kp) {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub kp).Msg × Wp))
  (cs : OnBytes.Codes) (l : List (OnBytes.OracleShape × ℕ))
  (iJ : R.Sh.Cf.J → (sigOf cs l).Ent) (iQ : R.Sh.Cf.Q → (sigOf cs l).Ent)
  (t : ℕ) (w₀ : (Hd.foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "LocK" => (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc

variable (W₀ : OnBytes.SwitchFrame) (k₀ : OnBytes.KeptPlace) (mem row : R.Kp → ℕ)
  (aOf : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.K → ℕ)
  (iOf : ∀ k, ((closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.o k).Z.S → ℕ)

/-- **Two seeds that fit have one matrix**, where the carrying is one to one. -/
theorem mat_of_fits (St : OnBytes.Statement) (k : (LocK).hd.K)
    (hinj : ∀ c c' : ((LocK).hd.o k).C.J → GE,
      pushTo ((LocK).hd.sJ k) c = pushTo ((LocK).hd.sJ k) c' → c = c')
    {sd sd' : ((LocK).hd.o k).Z.D}
    (h : SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k sd)
    (h' : SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k sd') :
    ((LocK).hd.o k).Z.mat sd = ((LocK).hd.o k).Z.mat sd' :=
  funext fun u => hinj _ _ ((h u).trans (h' u).symm)

/-- Where a seed fits, the chosen one does. -/
theorem smpMade_fits (x₀ : (LocK).hd.Smp) (St : OnBytes.Statement) (k : (LocK).hd.K)
    (h : ∃ sd, SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k sd) :
    SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k
      (smpMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf x₀ St k).1 := by
  unfold smpMade
  simp only [dif_pos h]
  exact h.choose_spec

/-- **The chosen seed collides just where a given fitting seed does.** -/
theorem clash_made_iff (x₀ : (LocK).hd.Smp) (St : OnBytes.Statement) (k : (LocK).hd.K)
    (hinj : ∀ c c' : ((LocK).hd.o k).C.J → GE,
      pushTo ((LocK).hd.sJ k) c = pushTo ((LocK).hd.sJ k) c' → c = c')
    {sd : ((LocK).hd.o k).Z.D}
    (h : SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k sd)
    (f : ((LocK).hd.o k).C.Word) :
    ((LocK).hd.o k).ClashW f
        (smpMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf x₀ St k).1 ↔
      ((LocK).hd.o k).ClashW f sd :=
  clashW_of_mat _ f (mat_of_fits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k hinj
    (smpMade_fits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf x₀ St k ⟨sd, h⟩) h)

/-- **So of the decoder with a sample**: at the held sample as made, and at a given fitting seed
with the same answers. -/
theorem dec_made_eq (x₀ : (LocK).hd.Smp) (St : OnBytes.Statement) (k : (LocK).hd.K)
    (hinj : ∀ c c' : ((LocK).hd.o k).C.J → GE,
      pushTo ((LocK).hd.sJ k) c = pushTo ((LocK).hd.sJ k) c' → c = c')
    {sd : ((LocK).hd.o k).Z.D}
    (h : SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k sd)
    (f : ((LocK).hd.o k).C.Word) :
    ((LocK).hd.o k).decW f
        (smpMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf x₀ St k) =
      ((LocK).hd.o k).decW f
        (sd, (smpMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf x₀ St k).2) :=
  decW_of_mat _ f (mat_of_fits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k hinj
    (smpMade_fits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf x₀ St k ⟨sd, h⟩) h) _

end General

section Held
variable (cs : Codes) (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop)
  [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)
  (kq : Fin l.length → Prop) (num : {a // kp a} → ℕ)

set_option quotPrecheck false in
local notation "hP" => heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq
set_option quotPrecheck false in
local notation:max "aK " k:max => (⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ : {a // kp a})
set_option quotPrecheck false in
local notation "RK" => (rowsPort cs l mem s e oM oZ hM hZ).keep kp

/-- **At the caller of the kept messages the carrying is one to one**: a kept member has no mask
row, and each entry of its main table has a slot of its own. -/
theorem push_held_inj (k : {a // (hP).cl a}) (c c' : (portCode cs (l.get k.1.1).1).J → GE)
    (h : pushTo ((hP).sJ k) c = pushTo ((hP).sJ k) c') : c = c' := by
  funext i
  rcases i with x | y
  · rw [← push_held_at cs l mem s e oM oZ hM hZ kp h1 h0 kq k c x, h, push_held_at]
  · have hz : (l.get k.1.1).1.maskRows = 0 := h0 ⟨k.1.1, k.2.fst⟩ k.2.snd
    exact absurd y.1.isLt (by omega)

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort cs l mem s e oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort cs l mem s e oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs l).sub kq).Msg × Wp))
  (cs' : Codes) (l' : List (OracleShape × ℕ)) (W : SwitchFrame) (plOf : {a // kp a} → KeptPlace)
  (jN : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.Cf.J → (sigOf cs' l').Ent)
  (qN : ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.Cf.Q → (sigOf cs' l').Ent)
  (t : ℕ)
  (w₀ : ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).tgt.W)
  (k₀ : KeptPlace)

set_option quotPrecheck false in
local notation "locK" => (closeSel (hP) Sb sl Z A₀ cs' l' jN qN t w₀).loc
set_option quotPrecheck false in
local notation "smpM" => smpMade (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
  (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
  (fun k => num (aK k)) (fun _ _ => 0)

/-- **At the caller of the kept messages**: no premise on the carrying is left. -/
theorem clash_made_held (x₀ : (locK).hd.Smp) (St : Statement) (k : {a // (hP).cl a})
    {sd : ((locK).hd.o k).Z.D}
    (h : SeedFits (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
      (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
      (fun k => num (aK k)) (fun _ _ => 0) St k sd)
    (f : ((locK).hd.o k).C.Word) :
    ((locK).hd.o k).ClashW f ((smpM) x₀ St k).1 ↔ ((locK).hd.o k).ClashW f sd :=
  clash_made_iff (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
    (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
    (fun k => num (aK k)) (fun _ _ => 0) x₀ St k
    (push_held_inj cs l mem s e oM oZ hM hZ kp h1 h0 kq k) h f

/-- The like of the decoder with a sample. -/
theorem dec_made_held (x₀ : (locK).hd.Smp) (St : Statement) (k : {a // (hP).cl a})
    {sd : ((locK).hd.o k).Z.D}
    (h : SeedFits (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
      (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
      (fun k => num (aK k)) (fun _ _ => 0) St k sd)
    (f : ((locK).hd.o k).C.Word) :
    ((locK).hd.o k).decW f ((smpM) x₀ St k) = ((locK).hd.o k).decW f (sd, ((smpM) x₀ St k).2) :=
  dec_made_eq (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
    (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
    (fun k => num (aK k)) (fun _ _ => 0) x₀ St k
    (push_held_inj cs l mem s e oM oZ hM hZ kp h1 h0 kq k) h f

/-- **THE CHOSEN SEED COLLIDES JUST WHERE THE SEED WHOSE SAMPLE ROW IS STORED, TYPED, DOES**: from
the invariant and public facts. -/
theorem clash_made_sampled (x₀ : (locK).hd.Smp) (St : Statement)
    (hG : K2.SampleGoodS St) (hcs : St.codes = cs)
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hmem : ∀ a, W.kept[num a]? = some (plOf a))
    (hrb : ∀ a : {a // kp a}, (plOf a).rowBits = k1 (l.get a.1.1).1)
    (ha : ∀ a : {a // kp a}, (l.get a.1.1).1.answers = 1)
    (hc : ∀ a : {a // kp a}, CaseE (l.get a.1.1).1 ∨ CaseF (l.get a.1.1).1)
    (hx : ∀ a : {a // kp a}, ∃ x, St.oracles[(plOf a).old]? = some x ∧
      x.shape = (l.get a.1.1).1 ∧ x.sampleRows.size ≠ 0)
    (k : {a // (hP).cl a}) :
    ∃ (seed : SampleSeed) (row : OnBytes.Row) (y : E) (β : GEˣ),
      Send.form cs (l.get k.1.1).1 (plOf (aK k)).old seed 0 = some row ∧
      (samplesOf St (plOf (aK k)))[0]? = some { row with target := y } ∧
      (β : GE) = readE seed.beta ∧
      ∀ f : ((locK).hd.o k).C.Word,
        ((locK).hd.o k).ClashW f ((smpM) x₀ St k).1 ↔
          ((locK).hd.o k).ClashW f (readP (bitsZ cs (l.get k.1.1).1) seed.z, β) := by
  obtain ⟨x, x1, x2, x3⟩ := hx (aK k)
  obtain ⟨seed, row, y, β, a1, a2, a3, a4⟩ :=
    stored_of_goodS cs l mem s e oM oZ hM hZ kp h1 h0 kq plOf St hG hcs k x x1 x2 x3 (ha (aK k))
  exact ⟨seed, row, y, β, a1, a2, a4, fun f =>
    clash_made_held cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W jN qN t w₀ k₀ x₀
      St k (seedFits_of_stored cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W plOf jN
        qN t w₀ k₀ St k inj hmem hrb (ha (aK k)) (hc (aK k)) seed row y β a1 a2 a3 a4) f⟩

end Held

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.val_of_mat
#print axioms VerifiableInference.Desc.First.K2Hands.clashW_of_mat
#print axioms VerifiableInference.Desc.First.K2Hands.pick_congr
#print axioms VerifiableInference.Desc.First.K2Hands.decMin_of_ev
#print axioms VerifiableInference.Desc.First.K2Hands.decW_of_mat
#print axioms VerifiableInference.Desc.First.K2Hands.mat_of_fits
#print axioms VerifiableInference.Desc.First.K2Hands.smpMade_fits
#print axioms VerifiableInference.Desc.First.K2Hands.clash_made_iff
#print axioms VerifiableInference.Desc.First.K2Hands.dec_made_eq
#print axioms VerifiableInference.Desc.First.K2Hands.push_held_inj
#print axioms VerifiableInference.Desc.First.K2Hands.clash_made_held
#print axioms VerifiableInference.Desc.First.K2Hands.dec_made_held
#print axioms VerifiableInference.Desc.First.K2Hands.clash_made_sampled
