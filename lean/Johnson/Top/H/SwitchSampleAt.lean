-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchSampleAt.lean: a held message's old sample row, as the typed code switch carries
it to the open word's entries, is the vector that the join to the program's text asks for.

Johnson/Top/H/SwitchHeldPush.lean reads the carried row entry by entry: at a kept slot of the
member, the coefficient at that entry; elsewhere 0. Johnson/Desc/K12/Law/FormPortZE.lean has the
library's sample row against the program's row `Send.form`, for main rows over the base field and
over the extension field. (Near kin: `coef_port_main`, Johnson/Desc/K1/Law/Port4.lean, with
`form_eq`, FormEq.lean there: the same two rows held together through that folder's own form of the
row, under premises on the codes' lengths and the shape; those files stand over a block's text,
which this file does not import.) The join to the text
(Johnson/Top/H0/K2Hands/KeptFormJoin.lean) speaks of one vector on all entries, `slotVec`: the
entries of a form on the slots of the member with a given number in the frame, 0 elsewhere. Here the
two are shown equal, as functions, at the programs' shapes (`heldPort`,
Johnson/Top/H/SwitchKept.lean) and the slots' readings of Johnson/Top/H/SwitchKeptIs.lean.
Statements and proofs.
Main names:
  `sample_held_vec`: the library's sample row at the seed's point and factor, read, carried along
    `hd.sJ`, is `slotVec` at the member's number, the shape's row bits and the form of the stored
    row (the program's row with any target; `stored_reads`,
    Johnson/Top/H0/K2Hands/FormOnReads.lean).
  `sample_clause_held`: at the caller of the kept messages, for every held message and answer: the
    frame's record of the member, the member's first stored sample row in a statement St, the
    typed sample's value as that row's target, and the carried row as `slotVec`: the shape in which
    the join to the text asks it (the clause `sample` of `FrontAt`,
    Johnson/Top/H0/K2Hands/TiePaid.lean, which is not imported here).
Limits: one answer; no mask row (a held message has none). The main rows may stand over either
field (`CaseE` or `CaseF`, as the library's test on a sending asks). The seed's point may be longer
than the cube has bits, as it is where a sending's messages have cubes of different sizes
(`form_take`, OnBytes/Slice/BlkSendTake.lean); the typed seed is its first coordinates, read.
Premises of the second statement, none
paid here: the kept members' numbers in the frame differ; the frame has the record plOf at the
number num, with the shape's row bits; `Slots`; and, member by member, that the first stored row in
St is `Send.form` at a seed with some target, and that the typed held sample is that seed, read,
with that target, read. St is a letter: nothing says that it is a statement of a run.

-/
import Johnson.Top.H.SwitchHeldPush
import Johnson.Top.H.SwitchKeptIs
import Johnson.Top.H0.K2Hands.KeptFormJoin
import Johnson.Top.H0.K2Hands.FormOnReads
import OnBytes.Slice.BlkSendTake
import Johnson.Desc.K12.Law.FormPortZE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack VerifiableInference.Desc.First.K2Hands

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

/-- **An old sample's row, carried to the open word's entries, as one vector**: row: the row that
the program makes for the held message (number o) at the seed; the typed seed is the first
coordinates of the seed's point, as many as the cube has, and the factor, read. The carried row is
the vector that has the entries of the stored row's form on the slots of the member's number, and 0
elsewhere. The stored row is the program's with any target y. -/
theorem sample_held_vec (k : {a // (hP).cl a}) (o : ℕ) (seed : SampleSeed) (row : Row)
    (h : Send.form cs (l.get k.1.1).1 o seed 0 = some row) (ha : (l.get k.1.1).1.answers = 1)
    (hc : CaseE (l.get k.1.1).1 ∨ CaseF (l.get k.1.1).1)
    (hz : bitsZ cs (l.get k.1.1).1 ≤ seed.z.length) (β : GEˣ)
    (hβ : (β : GE) = readE seed.beta) (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (y : E) :
    pushTo ((hP).sJ k)
        ((portZ cs (l.get k.1.1).1).mat (readP (bitsZ cs (l.get k.1.1).1) seed.z, β) ()) =
      slotVec s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp
        (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
        (num (aK k)) (k1 (l.get k.1.1).1) (formOn { row with target := y }) := by
  have eC : (cMain cs (l.get k.1.1).1).l = s.C.l :=
    congrArg Fmt.M1.Code.l (hM k.1.1 k.2.fst (h1 ⟨k.1.1, k.2.fst⟩ k.2.snd))
  have h' : Send.form cs (l.get k.1.1).1 o
      { seed with z := seed.z.take (bitsZ cs (l.get k.1.1).1) } 0 = some row :=
    (form_take cs _ o seed 0 _ (cube_bits cs (l.get k.1.1).1).le).trans h
  have hz' : (seed.z.take (bitsZ cs (l.get k.1.1).1)).length = bitsZ cs (l.get k.1.1).1 := by
    rw [List.length_take]
    exact Nat.min_eq_left hz
  rw [← readP_take (bitsZ cs (l.get k.1.1).1) seed.z]
  funext n
  rcases n with ⟨_ | ⟨a, r⟩, j⟩ | q
  · rw [push_held_off cs l mem s e oM oZ hM hZ kp h1 h0 kq k _ _ fun x => by
      rw [heldPort_sJ]
      intro q
      cases q]
    rfl
  · by_cases hm : num a = num (aK k)
    · obtain rfl : a = aK k := inj _ _ hm
      have en : (Sum.inl (some ⟨aK k, r⟩, j) :
          ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Sh.Cf.J) =
          (hP).sJ k (.inl (r, Fin.cast eC.symm j)) := by
        rw [heldPort_sJ]
        rfl
      rw [en, push_held_at, ← en]
      show _ = if num (aK k) = num (aK k) then
        formAt (formOn { row with target := y }) (r.val + 2 ^ _ * j.val) else 0
      rw [if_pos rfl]
      rw [stored_reads h (h0 ⟨k.1.1, k.2.fst⟩ k.2.snd) y]
      exact (H2K.Pin.form_portZ cs _ o _ row h' ha hc hz' β hβ
        (.inl (r, Fin.cast eC.symm j))).symm
    · rw [push_held_off cs l mem s e oM oZ hM hZ kp h1 h0 kq k _ _ fun x => by
        rw [heldPort_sJ]
        intro q
        exact hm (congrArg num (congrArg Sigma.fst
          (Option.some.inj (congrArg Prod.fst (Sum.inl.inj q)))).symm)]
      show (0 : GE) = if num a = num (aK k) then _ else 0
      rw [if_neg hm]
  · rw [push_held_off cs l mem s e oM oZ hM hZ kp h1 h0 kq k _ _ fun x => by
      rw [heldPort_sJ]
      intro q
      cases q]
    rfl

variable [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
  (sl : ∀ b, Slf GE (Sb b) (rowsPort cs l mem s e oM oZ hM hZ).G.C.J)
  (Z : Evader GE ((rowsPort cs l mem s e oM oZ hM hZ).G.Row B)) {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ (((sigOf cs l).sub kq).Msg × Wp))
  (cs' : Codes) (l' : List (OracleShape × ℕ)) (W : SwitchFrame) (plOf : {a // kp a} → KeptPlace)
  (Ft : Fit cs' l' s W (slotNum cs l mem s e oM oZ hM hZ kp num)
    (slotRow cs l mem s e oM oZ hM hZ kp) (slotPl cs l mem s e oM oZ hM hZ kp plOf))
  (t : ℕ)
  (w₀ : ((heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq).foldD Sb sl Z A₀).tgt.W)

set_option quotPrecheck false in
local notation "hdK" => (closeSel (hP) Sb sl Z A₀ cs' l'
  (iJ s W (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
    (slotPl cs l mem s e oM oZ hM hZ kp plOf) cs' l' Ft.nameJ)
  (iQ s W (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp) cs' l'
    Ft.nameQ) t w₀).loc.hd

/-- **The old samples at the caller of the kept messages, in the shape in which the join to the text
asks them**: xs: the typed held samples; St: a statement; ids: the new messages' numbers. -/
theorem sample_clause_held (St : Statement) (ids : ℕ → ℕ) (xs : (hdK).Smp)
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hmem : ∀ a, W.kept[num a]? = some (plOf a))
    (hrb : ∀ a : {a // kp a}, (plOf a).rowBits = k1 (l.get a.1.1).1)
    (hSl : ∀ a, Slots s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp cs' l' W ids
      (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp) (num a)
      (plOf a))
    (ha : ∀ a : {a // kp a}, (l.get a.1.1).1.answers = 1)
    (hc : ∀ a : {a // kp a}, CaseE (l.get a.1.1).1 ∨ CaseF (l.get a.1.1).1)
    (hst : ∀ k : {a // (hP).cl a}, ∃ (seed : SampleSeed) (row : Row) (y : E) (β : GEˣ),
      Send.form cs (l.get k.1.1).1 (plOf (aK k)).old seed 0 = some row ∧
      (samplesOf St (plOf (aK k)))[0]? = some { row with target := y } ∧
      bitsZ cs (l.get k.1.1).1 ≤ seed.z.length ∧ (β : GE) = readE seed.beta ∧
      (xs k).1 = (readP (bitsZ cs (l.get k.1.1).1) seed.z, β) ∧ (xs k).2 () = readE y) :
    ∀ ks : Σ k, ((hdK).o k).Z.S, ∃ (k : KeptPlace) (smp : Row),
      W.kept[num (aK ks.1)]? = some k ∧ (samplesOf St k)[0]? = some smp ∧
      Slots s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp cs' l' W ids
        (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
        (num (aK ks.1)) k ∧
      (xs ks.1).2 ks.2 = readE smp.target ∧
      pushTo ((hdK).sJ ks.1) (((hdK).o ks.1).Z.mat (xs ks.1).1 ks.2) =
        slotVec s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp
          (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
          (num (aK ks.1)) k.rowBits (formOn smp) := by
  rintro ⟨k, u⟩
  obtain ⟨seed, row, y, β, h, hs, hz, hβ, hx, hy⟩ := hst k
  refine ⟨plOf (aK k), { row with target := y }, hmem _, hs, hSl _, hy, ?_⟩
  rw [hrb]
  show pushTo ((hP).sJ k) ((portZ cs (l.get k.1.1).1).mat (xs k).1 ()) = _
  rw [hx]
  exact sample_held_vec cs l mem s e oM oZ hM hZ kp h1 h0 kq num k _ seed row h (ha (aK k))
    (hc (aK k)) hz β hβ inj y

end Johnson.Top.H

#print axioms Johnson.Top.H.sample_held_vec
#print axioms Johnson.Top.H.sample_clause_held
