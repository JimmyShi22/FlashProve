-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchSeedFits.lean: code switching: THAT A TYPED SEED FITS A KEPT MEMBER's STORED
SAMPLE ROW (`SeedFits`, Johnson/Top/H/SwitchInXMade.lean), at the caller of the kept messages, at
any two maps of names, FROM AN INVARIANT OF THE VERIFIER's STATE; and that a yes of the kind's
decision keeps that invariant.

Why. The typed statement in front of the switch is made off the verifier's state (`inXMade`): a held
old out-of-domain sample's seed is chosen among the typed seeds that fit the stored row. That one
fits is owed. It does where the stored row is the program's `Send.form` at a seed whose point has at
least the cube's coordinates and whose factor, read, is not 0 (`sample_held_vec`,
Johnson/Top/H/SwitchSampleAt.lean). `Send.form` tests neither (OnBytes/Iop/Send.lean: "Not tested
here"), and the invariant `SampleGood` (Johnson/Top/H0/K2Hears/SampleGood.lean) says neither. So the
invariant is stated again with three clauses more on each seed.
  `SampleGoodS St`: every message of St with a stored sample row has, for some list of seeds, the
  rows `RowsAre`; each seed's point has at least the message's cube's coordinates; each seed's
  factor is not the zero element and is in canonical form.
  `SampleGoodS.good`: it gives `SampleGood`.
  `seedsOf_beta`: a factor that `Send.seedsOf` cuts is one of the elements that it was given.
  `sampleGoodS_kept`: at a yes (`AtYes`), where round 1's drawn elements are in canonical form: of
  the front's statement it gives it of the state behind.
  `stored_of_goodS`: from it, at a kept member whose message in St has the typed shape, one answer
  and a stored row: the seed, the row, the target and the unit that `sample_held_vec` asks.
  `seedFits_of_stored`: from these four: the typed seed (the point's first coordinates, read; the
  unit) fits.
  `seedFits_of_goodS`: the two in a row: premise h3 of `xcMade_sample`.
  `sample_made_of_goodS`: so the clause "sample" of `FrontAtL` at what is made, from the invariant
  and the public facts.
Limits. K2's share of the invariant alone: that the other kinds keep it, and that it holds at the
chain's start, is not typed. That a round's drawn elements are in canonical form is a premise. The
public facts (the frame has the member at its number, with the shape's row bits; the numbers differ;
one answer; the case of the pad; the message's shape) are premises. One answer. Nothing on soundness
or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H.SwitchInXMade
import Johnson.Top.H.SwitchSampleFront
import Johnson.Top.H0.K2Hears.SampleGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model OnBytes.Slice
open _root_.Tw.K2 (switchNotices sendByL8)

/-- **The invariant, with what the typed reading of a seed spends.** -/
def SampleGoodS (St : Statement) : Prop :=
  ∀ (o : Nat) (x : OnBytes.Oracle), St.oracles[o]? = some x → x.sampleRows.size ≠ 0 →
    ∃ seeds, RowsAre St.codes x.shape o seeds x.sampleRows ∧
      ∀ sd ∈ seeds, (Send.cube St.codes x.shape).bits ≤ sd.z.length ∧
        isZeroE sd.beta = false ∧ okE sd.beta = true

theorem SampleGoodS.good {St : Statement} (h : SampleGoodS St) : SampleGood St :=
  fun o x hx hs => (h o x hx hs).imp fun _ q => q.1

/-- A factor that `Send.seedsOf` cuts is one of the elements that it was given. -/
theorem seedsOf_beta (bits : Nat) : ∀ (n : Nat) (l : List E) (seeds : List SampleSeed),
    Send.seedsOf bits n l = some seeds → ∀ sd ∈ seeds, sd.beta ∈ l
  | 0, [], seeds, h, sd, hs => by
    simp only [Send.seedsOf, Option.some.injEq] at h
    subst h
    cases hs
  | 0, _ :: _, seeds, h, _, _ => by simp [Send.seedsOf] at h
  | n + 1, l, seeds, h, sd, hs => by
    unfold Send.seedsOf at h
    split at h
    · cases h
    · rename_i beta rest hd
      obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.1 h
      have hsub : ∀ e ∈ beta :: rest, e ∈ l := fun e he => List.mem_of_mem_drop (hd ▸ he)
      rcases List.mem_cons.1 hs with rfl | hs
      · exact hsub _ (List.mem_cons_self)
      · exact hsub _ (List.mem_cons_of_mem _ (seedsOf_beta bits n rest t ht sd hs))

/-- **A yes keeps it, and makes it at the new messages**, where round 1's drawn elements are in
canonical form. -/
theorem sampleGoodS_kept {p : P2} {s s' : S} {r₁ r₂ : Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    {x : _root_.Tw.K2.Front} {y : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E}
    {rows : List OnBytes.Row} {G : Group} {c : Code}
    (A : AtYes p s s' r₁ r₂ gs x y S3 Y rows G c)
    (hok : ∀ e ∈ r₁.drawn.elems.map E.ofTriple, okE e = true) (h : SampleGoodS x.st) :
    SampleGoodS s'.st := by
  intro o xo hxo hsz
  have T := A.same.trans A.tables
  have hcod : s'.st.codes = x.st.codes := T.codes.trans A.sent.codes
  have hsh := T.shape o
  have hsm := T.samples o
  rw [hxo] at hsh hsm
  simp only [Option.map_some] at hsh hsm
  rw [hcod]
  by_cases ho : o < x.st.oracles.size
  · rw [A.sent.old o ho] at hsh hsm
    obtain ⟨x0, hx0, e1⟩ := Option.map_eq_some_iff.1 hsh.symm
    obtain ⟨x1, hx1, e2⟩ := Option.map_eq_some_iff.1 hsm.symm
    rw [hx0] at hx1
    obtain rfl := Option.some.inj hx1
    rw [← e1, ← e2]
    exact h o x0 hx0 (by rw [e2]; exact hsz)
  · obtain ⟨i, rfl⟩ : ∃ i, o = x.st.oracles.size + i := ⟨o - x.st.oracles.size, by omega⟩
    obtain ⟨bits, answers, seeds, hcut, hnz, hall, hnone⟩ := sent_rows A.sentBy
    rw [A.sent.shape i] at hsh
    obtain ⟨n, hn, e1⟩ := Option.map_eq_some_iff.1 hsh.symm
    by_cases ha : n.shape.answers = 0
    · rw [hnone i n hn ha] at hsm
      have e2 := Option.some.inj hsm
      rw [e2] at hsz
      exact absurd rfl hsz
    · obtain ⟨hb, rws, hr, hR⟩ := hall i n hn ha
      rw [hr] at hsm
      have e2 := Option.some.inj hsm
      rw [← e1, e2]
      exact ⟨seeds, hR, fun sd hsd => ⟨by rw [seedsOf_len bits _ _ _ hcut sd hsd]; exact hb,
        hnz sd hsd, hok _ (seedsOf_beta bits _ _ _ hcut sd hsd)⟩⟩

end VerifiableInference.Desc.First.K2

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

variable (cs : Codes) (l : List (OracleShape × ℕ)) (mem : Fin l.length → Prop)
  [DecidablePred mem] (s : Sg) (e : ℕ) (oM oZ : Fin l.length → ℕ)
  (hM : ∀ i, mem i → (l.get i).1.mainRows ≠ 0 → cMain cs (l.get i).1 = s.C)
  (hZ : ∀ i, mem i → (l.get i).1.maskRows ≠ 0 → cMask cs (l.get i).1 = s.Z)
  (kp : {i // mem i} → Prop) [DecidablePred kp]
  (h1 : ∀ a, kp a → (l.get a.1).1.mainRows ≠ 0) (h0 : ∀ a, kp a → (l.get a.1).1.maskRows = 0)
  (kq : Fin l.length → Prop) (num : {a // kp a} → ℕ)
  [DecidablePred kq] {B Kc St₀ Wp : Type} [Fintype B] (Sb : B → Type)
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
local notation "hP" => heldPort cs l mem s e oM oZ hM hZ kp h1 h0 kq
set_option quotPrecheck false in
local notation:max "aK " k:max => (⟨⟨k.1.1, k.2.fst⟩, k.2.snd⟩ : {a // kp a})
set_option quotPrecheck false in
local notation "RK" => (rowsPort cs l mem s e oM oZ hM hZ).keep kp

omit [DecidablePred kq] in
/-- **From the invariant: the seed, the row, the target and the unit** at a kept member whose
message in St has the typed shape, one answer and a stored row. -/
theorem stored_of_goodS (St : Statement) (hG : K2.SampleGoodS St) (hcs : St.codes = cs)
    (k : {a // (hP).cl a}) (x : OnBytes.Oracle)
    (hx : St.oracles[(plOf (aK k)).old]? = some x) (hsh : x.shape = (l.get k.1.1).1)
    (hn : x.sampleRows.size ≠ 0) (ha : (l.get k.1.1).1.answers = 1) :
    ∃ (seed : SampleSeed) (row : OnBytes.Row) (y : E) (β : GEˣ),
      Send.form cs (l.get k.1.1).1 (plOf (aK k)).old seed 0 = some row ∧
      (samplesOf St (plOf (aK k)))[0]? = some { row with target := y } ∧
      bitsZ cs (l.get k.1.1).1 ≤ seed.z.length ∧ (β : GE) = readE seed.beta := by
  obtain ⟨seeds, ⟨-, hrows⟩, hall⟩ := hG _ x hx hn
  obtain ⟨seed, row, y, hsd, hf, hr⟩ := hrows 0 (by rw [hsh, ha]; exact Nat.one_pos)
  obtain ⟨hz, hb, ho⟩ := hall seed (List.mem_of_getElem? hsd)
  rw [hcs, hsh] at hf hz
  have hne : readE seed.beta ≠ 0 := fun q => by
    rw [(isZeroE_iff seed.beta ho).2 q] at hb
    cases hb
  refine ⟨seed, row, y, Units.mk0 _ hne, hf, ?_, by rw [← cube_bits]; exact hz, rfl⟩
  unfold samplesOf
  rw [Array.getD_eq_getD_getElem?, hx, Option.getD_some, Array.getElem?_toList]
  exact hr

/-- The frame's entry for a held message's member is the member's. -/
theorem keptOfN_held (hmem : ∀ a, W.kept[num a]? = some (plOf a)) (k : {a // (hP).cl a}) :
    keptOfN (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀ (fun k => num (aK k)) k =
      plOf (aK k) := by
  unfold keptOfN
  rw [List.getD_eq_getElem?_getD, hmem, Option.getD_some]

/-- **The typed seed fits**: the first coordinates of the seed's point, read, and the unit. -/
theorem seedFits_of_stored (St : Statement) (k : {a // (hP).cl a})
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hmem : ∀ a, W.kept[num a]? = some (plOf a))
    (hrb : ∀ a : {a // kp a}, (plOf a).rowBits = k1 (l.get a.1.1).1)
    (ha : (l.get k.1.1).1.answers = 1) (hc : CaseE (l.get k.1.1).1 ∨ CaseF (l.get k.1.1).1)
    (seed : SampleSeed) (row : OnBytes.Row) (y : E) (β : GEˣ)
    (h : Send.form cs (l.get k.1.1).1 (plOf (aK k)).old seed 0 = some row)
    (hs : (samplesOf St (plOf (aK k)))[0]? = some { row with target := y })
    (hz : bitsZ cs (l.get k.1.1).1 ≤ seed.z.length) (hβ : (β : GE) = readE seed.beta) :
    SeedFits (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
      (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
      (fun k => num (aK k)) (fun _ _ => 0) St k
      (readP (bitsZ cs (l.get k.1.1).1) seed.z, β) := by
  intro u
  have ek := keptOfN_held cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W plOf jN qN t
    w₀ k₀ hmem k
  have er : rowOfS (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀ (fun k => num (aK k))
      (fun _ _ => 0) St k u = { row with target := y } := by
    unfold rowOfS
    rw [ek, List.getD_eq_getElem?_getD, hs, Option.getD_some]
  rw [ek, er, hrb]
  exact sample_held_vec cs l mem s e oM oZ hM hZ kp h1 h0 kq num k _ seed row h ha hc hz β hβ inj y

/-- **Premise h3 of `xcMade_sample` from the invariant and public facts.** -/
theorem seedFits_of_goodS (St : Statement) (hG : K2.SampleGoodS St) (hcs : St.codes = cs)
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hmem : ∀ a, W.kept[num a]? = some (plOf a))
    (hrb : ∀ a : {a // kp a}, (plOf a).rowBits = k1 (l.get a.1.1).1)
    (ha : ∀ a : {a // kp a}, (l.get a.1.1).1.answers = 1)
    (hc : ∀ a : {a // kp a}, CaseE (l.get a.1.1).1 ∨ CaseF (l.get a.1.1).1)
    (hx : ∀ a : {a // kp a}, ∃ x, St.oracles[(plOf a).old]? = some x ∧
      x.shape = (l.get a.1.1).1 ∧ x.sampleRows.size ≠ 0) :
    ∀ k : {a // (hP).cl a}, ∃ sd,
      SeedFits (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
        (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
        (fun k => num (aK k)) (fun _ _ => 0) St k sd := by
  intro k
  obtain ⟨x, x1, x2, x3⟩ := hx (aK k)
  obtain ⟨seed, row, y, β, a1, a2, a3, a4⟩ :=
    stored_of_goodS cs l mem s e oM oZ hM hZ kp h1 h0 kq plOf St hG hcs k x x1 x2 x3 (ha (aK k))
  exact ⟨_, seedFits_of_stored cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W plOf jN
    qN t w₀ k₀ St k inj hmem hrb (ha (aK k)) (hc (aK k)) seed row y β a1 a2 a3 a4⟩

set_option quotPrecheck false in
local notation "locK" => (closeSel (hP) Sb sl Z A₀ cs' l' jN qN t w₀).loc
set_option quotPrecheck false in
local notation "xcM" => xcMade (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
  (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
  (slotPl cs l mem s e oM oZ hM hZ kp plOf) (fun k => num (aK k)) (fun _ _ => 0)

/-- **THE CLAUSE "sample" OF `FrontAtL` AT WHAT IS MADE, FROM THE INVARIANT AND PUBLIC FACTS**, at
the caller of the kept messages. -/
theorem sample_made_of_goodS (x₀ : (locK).hd.Smp) (fx : _root_.Tw.K2.Front)
    (hG : K2.SampleGoodS fx.st) (hcs : fx.st.codes = cs)
    (inj : ∀ a a' : {a // kp a}, num a = num a' → a = a')
    (hmem : ∀ a, W.kept[num a]? = some (plOf a))
    (hrb : ∀ a : {a // kp a}, (plOf a).rowBits = k1 (l.get a.1.1).1)
    (ha : ∀ a : {a // kp a}, (l.get a.1.1).1.answers = 1)
    (hc : ∀ a : {a // kp a}, CaseE (l.get a.1.1).1 ∨ CaseF (l.get a.1.1).1)
    (hx : ∀ a : {a // kp a}, ∃ x, fx.st.oracles[(plOf a).old]? = some x ∧
      x.shape = (l.get a.1.1).1 ∧ x.sampleRows.size ≠ 0) :
    ∀ ks : Σ k, ((locK).hd.o k).Z.S, ∃ (k : KeptPlace) (smp : OnBytes.Row),
      W.kept[num (aK ks.1)]? = some k ∧ (samplesOf fx.st k)[0]? = some smp ∧
        (((xcM) x₀ fx).2 ks.1).2 ks.2 = readE smp.target ∧
        pushTo ((locK).hd.sJ ks.1) (((locK).hd.o ks.1).Z.mat (((xcM) x₀ fx).2 ks.1).1 ks.2) =
          slotVec s ((rowsPort cs l mem s e oM oZ hM hZ).keep kp).Kp
            (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
            (num (aK ks.1)) k.rowBits (formOn smp) :=
  xcMade_sample (RK) (hP) Sb sl Z A₀ cs' l' jN qN t w₀ W k₀
    (slotNum cs l mem s e oM oZ hM hZ kp num) (slotRow cs l mem s e oM oZ hM hZ kp)
    (slotPl cs l mem s e oM oZ hM hZ kp plOf) (fun k => num (aK k)) (fun _ _ => 0) x₀ fx
    (fun k => (List.getElem?_eq_some_iff.1 (hmem (aK k))).1)
    (fun k _ => by
      rw [keptOfN_held cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W plOf jN qN t w₀
        k₀ hmem k]
      obtain ⟨x, x1, x2, x3⟩ := hx (aK k)
      obtain ⟨_, _, _, _, -, a2, -, -⟩ := stored_of_goodS cs l mem s e oM oZ hM hZ kp h1 h0 kq plOf
        fx.st hG hcs k x x1 x2 x3 (ha (aK k))
      exact (List.getElem?_eq_some_iff.1 a2).1)
    (seedFits_of_goodS cs l mem s e oM oZ hM hZ kp h1 h0 kq num Sb sl Z A₀ cs' l' W plOf jN qN t w₀
      k₀ fx.st hG hcs inj hmem hrb ha hc hx)

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2.SampleGoodS.good
#print axioms VerifiableInference.Desc.First.K2.seedsOf_beta
#print axioms VerifiableInference.Desc.First.K2.sampleGoodS_kept
#print axioms VerifiableInference.Desc.First.K2Hands.stored_of_goodS
#print axioms VerifiableInference.Desc.First.K2Hands.keptOfN_held
#print axioms VerifiableInference.Desc.First.K2Hands.seedFits_of_stored
#print axioms VerifiableInference.Desc.First.K2Hands.seedFits_of_goodS
#print axioms VerifiableInference.Desc.First.K2Hands.sample_made_of_goodS
