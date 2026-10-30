-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/SwitchInXMade.lean: code switching: THE TYPED STATEMENT IN FRONT, MADE OFF THE
VERIFIER's STATE (the Lean type `Rec`); and the three clauses of `FrontAtL`
(Johnson/Top/H0/K2Hands/TieLight.lean) that read it, at what is made.

Why. The law of the code switch over its written text has a letter inX: from a verifier's state to
the typed statement in front of the switch. `FrontAtL` asks three things of it at the front fx that
the text makes of the state: the carried claim's value is the carried rows' target, read ("target");
its vector is the carried rows' vector ("vector"); each held old out-of-domain (OOD) sample (an OOD
seed and its OOD answers) has the stored rows' targets, read, as its OOD answers, and an OOD seed
whose sample rows, carried to the open word's entries, are the vectors of the stored rows' forms
("sample"). So far inX was made at toys alone. Here it is made once, general in the letters of the
structure `FrontAtL` itself.
  `keptOfN`, `rowOfS`: the frame's entry for a held message's member; a stored sample row of it in a
  statement. Where the frame has none: the letter k₀; where the statement has none: a default.
  `SeedFits`: a typed OOD seed whose rows, carried over, are the vectors of these stored rows'
  forms.
  `smpMade`: the held samples: such an OOD seed, BY CHOICE, where there is one; the OOD answers: the
  stored rows' targets, read.
  `xcMade`: the claim and the held samples off a front. `inXMade`: the statement in front off a
  verifier's state: through the front that the text makes of it.
  `xcMade_target`, `xcMade_vector`: the two clauses: by definition.
  `xcMade_sample`: the third, to its letter, where the frame has the member, the statement the rows,
  and an OOD seed fits.
  `frontAtL_made`: `FrontAtL` at what is made, from its other thirteen clauses and these three
  premises.
  `inXMade_at`: where the text makes a front of the state, what `FrontOnL` reads of inXMade is
  `xcMade` at that front.
Limits. DEFINITIONS BY MAKE, and three short laws. The OOD seed is chosen, not computed: NOBODY CAN
NAME IT. Beside the clause "sample" two more texts read it: the law's condition "no kept slot of the
open word has a collision at that seed" (`KeptFree`, Johnson/Top/H0/K2Caller/PlainGood.lean) and the
relaxed relation's decoder with a sample. That these do not feel the choice, since all seeds that
fit collide and decode alike, is Johnson/Top/H/SwitchSeedSame.lean's, at the caller of the kept
messages; it is not said here. That an OOD seed fits is a premise here (at the caller of the kept
messages: Johnson/Top/H/SwitchSeedFits.lean). x₀ and rest are letters: a placeholder where nothing
is made, and the parts of the statement that the three clauses do not read. W₀ is a letter: nothing
says that it is the frame of a place. Nothing on soundness or hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.H0.K2Hands.TieLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Hands
open OnBytes.Slice Cb Iop IOR Johnson.Pack Johnson.Top.H OnBytes.Tie.Pv.Switch

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
  (pl : R.Kp → OnBytes.KeptPlace) (aOf : (closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.K → ℕ)
  (iOf : ∀ k, ((closeSel Hd Sb sl Z A₀ cs l iJ iQ t w₀).loc.hd.o k).Z.S → ℕ)

/-- The frame's entry for a held message's member. -/
def keptOfN (k : (LocK).hd.K) : OnBytes.KeptPlace := W₀.kept.getD (aOf k) k₀

/-- A stored sample row of a held message's member, in a statement. -/
def rowOfS (St : OnBytes.Statement) (k : (LocK).hd.K) (u : ((LocK).hd.o k).Z.S) : OnBytes.Row :=
  (samplesOf St (keptOfN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf k)).getD (iOf k u) default

/-- **A typed seed fits the stored rows**: its sample rows, carried to the open word's entries, are
the vectors of the stored rows' forms. -/
def SeedFits (St : OnBytes.Statement) (k : (LocK).hd.K) (sd : ((LocK).hd.o k).Z.D) : Prop :=
  ∀ u, pushTo ((LocK).hd.sJ k) (((LocK).hd.o k).Z.mat sd u) =
    slotVec R.s R.Kp mem row (aOf k) (keptOfN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf k).rowBits
      (formOn (rowOfS R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf iOf St k u))

open Classical in
/-- **The held samples, made**: a seed that fits, by choice, where there is one, x₀'s else; the
answers are the stored rows' targets, read. -/
noncomputable def smpMade (x₀ : (LocK).hd.Smp) (St : OnBytes.Statement) : (LocK).hd.Smp := fun k =>
  (if h : ∃ sd, SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf St k sd then h.choose
    else (x₀ k).1,
    fun u => readE (rowOfS R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf iOf St k u).target)

/-- **The claim and the held samples, made off a front.** -/
noncomputable def xcMade (x₀ : (LocK).hd.Smp) (fx : _root_.Tw.K2.Front) :
    (LocK).Xc × (LocK).hd.Smp :=
  ((readE fx.f.rows.target, vecOf R.s R.Kp fx.f.rows row pl),
    smpMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf x₀ fx.st)

/-- The clause "target" of `FrontAtL`. -/
theorem xcMade_target (x₀ : (LocK).hd.Smp) (fx : _root_.Tw.K2.Front) :
    (xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf x₀ fx).1.1 =
      readE fx.f.rows.target := rfl

/-- The clause "vector" of `FrontAtL`. -/
theorem xcMade_vector (x₀ : (LocK).hd.Smp) (fx : _root_.Tw.K2.Front) :
    (xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf x₀ fx).1.2 =
      vecOf R.s R.Kp fx.f.rows row pl := rfl

/-- **The clause "sample" of `FrontAtL`, to its letter**: where the frame has each held message's
member, the front's statement the stored rows, and a typed seed fits them. -/
theorem xcMade_sample (x₀ : (LocK).hd.Smp) (fx : _root_.Tw.K2.Front)
    (h1 : ∀ k, aOf k < W₀.kept.length)
    (h2 : ∀ k u, iOf k u <
      (samplesOf fx.st (keptOfN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf k)).length)
    (h3 : ∀ k, ∃ sd, SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf fx.st k sd) :
    ∀ ks : Σ k, ((LocK).hd.o k).Z.S, ∃ (k : OnBytes.KeptPlace) (smp : OnBytes.Row),
      W₀.kept[aOf ks.1]? = some k ∧ (samplesOf fx.st k)[iOf ks.1 ks.2]? = some smp ∧
        ((xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf x₀ fx).2 ks.1).2 ks.2 =
          readE smp.target ∧
        pushTo ((LocK).hd.sJ ks.1) (((LocK).hd.o ks.1).Z.mat
            ((xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf x₀ fx).2 ks.1).1
            ks.2) =
          slotVec R.s R.Kp mem row (aOf ks.1) k.rowBits (formOn smp) := by
  rintro ⟨k, u⟩
  refine ⟨keptOfN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf k,
    rowOfS R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf iOf fx.st k u, ?_, ?_, rfl, ?_⟩
  · unfold keptOfN
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h1 k)]
    rfl
  · unfold rowOfS
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (h2 k u)]
    rfl
  · have e : ((xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf x₀ fx).2 k).1 =
        (h3 k).choose := dif_pos (h3 k)
    rw [e]
    exact (h3 k).choose_spec u

/-- **`FrontAtL` at what is made, from its other thirteen clauses**, word for word, and the three
premises on the old samples: so Lean holds the three ends against the structure's own fields. -/
theorem frontAtL_made (p : K2.P2) (s : Rec) (orc : ℕ → ℕ → List UInt64) (x₀ : (LocK).hd.Smp)
    (str : (LocK).C.ext.Str) (fx : _root_.Tw.K2.Front)
    (frameIs : K2.frameAt fx = some W₀) (z32 : W₀.zk.logN ≤ 32)
    (twoOld : ∀ (a a' : ℕ) (k k' : OnBytes.KeptPlace), W₀.kept[a]? = some k →
      W₀.kept[a']? = some k' → k.old = k'.old → a = a')
    (codes : fx.st.codes = cs) (keptPos : K2.KeptPos fx.T)
    (keptRows : fx.f.rows.keptRows = (W₀.kept.map (·.rows)).sum)
    (ell : ∀ (a : ℕ) (k : OnBytes.KeptPlace), W₀.kept[a]? = some k →
      (fx.st.codes.base.getD (fx.st.oracles.getD k.old default).shape.code default).ell =
        W₀.code.ell)
    (first : ∃ g0 : 0 < l.length, (l.get ⟨0, g0⟩).1 = fx.T.shape)
    (next : ∀ i (hi : i < fx.T.kept.size), ∃ h : 1 + i < l.length,
      (l.get ⟨1 + i, h⟩).1 = fx.T.kept[i].shape)
    (mainVars : ∀ v ∈ fx.f.rows.c.tensors, v.vars = W₀.code.logEll)
    (d0 : (fx.f.rows.d.getD 0 #[]).size ≤ W₀.zk.ell)
    (d1 : (fx.f.rows.d.getD 1 #[]).size ≤ W₀.zk.ell)
    (strIs : StrIs R Hd Sb sl Z A₀ cs l iJ iQ t w₀ p s fx orc
      (coordOf R.s R.Kp W₀ fx.f.rows mem row) str)
    (h1 : ∀ k, aOf k < W₀.kept.length)
    (h2 : ∀ k u, iOf k u <
      (samplesOf fx.st (keptOfN R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ aOf k)).length)
    (h3 : ∀ k, ∃ sd, SeedFits R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row aOf iOf fx.st k sd) :
    FrontAtL R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ p mem row pl aOf iOf s orc
      (xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf x₀ fx) str fx :=
  ⟨frameIs, z32, twoOld, codes, keptPos, keptRows, ell, first, next, mainVars, d0, d1, strIs, rfl,
    rfl, xcMade_sample R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf x₀ fx h1 h2 h3⟩

variable {Pw : Type} (Cw : LdCode GE Pw) (p : K2.P2)

/-- **The typed statement in front, made off a verifier's state**: through the front that the text
makes of it. rest: the carried part and the old open samples, which the three clauses do not read.
xc₀: what stands where the text makes no front. -/
noncomputable def inXMade (xc₀ : (LocK).Xc × (LocK).hd.Smp)
    (rest : Rec → St₀ × (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw).S.Smp)
    (s : Rec) : (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw).X :=
  ((match K2.frontAt p s with
    | some fx => xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf xc₀.2 fx
    | none => xc₀, (rest s).1), (rest s).2)

/-- **What `FrontOnL` reads of it** where the text makes a front of the state. -/
theorem inXMade_at (xc₀ : (LocK).Xc × (LocK).hd.Smp)
    (rest : Rec → St₀ × (Cb.Pv.SendLoc.stage (switchSel Hd Sb sl Z A₀ cs l iJ iQ t w₀ Cw).sw).S.Smp)
    (s : Rec) (fx : _root_.Tw.K2.Front) (h : K2.frontAt p s = some fx) :
    (inXMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf Cw p xc₀ rest s).1.1 =
      xcMade R Hd Sb sl Z A₀ cs l iJ iQ t w₀ W₀ k₀ mem row pl aOf iOf xc₀.2 fx := by
  unfold inXMade
  rw [h]

end VerifiableInference.Desc.First.K2Hands

#print axioms VerifiableInference.Desc.First.K2Hands.xcMade_target
#print axioms VerifiableInference.Desc.First.K2Hands.xcMade_vector
#print axioms VerifiableInference.Desc.First.K2Hands.xcMade_sample
#print axioms VerifiableInference.Desc.First.K2Hands.frontAtL_made
#print axioms VerifiableInference.Desc.First.K2Hands.inXMade_at
