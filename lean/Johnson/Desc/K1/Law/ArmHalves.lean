-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/ArmHalves.lean: K4's and K5's files' halves of the exchange across a segment's
second commitment, CALLED, each with what it still asks gathered in one structure with a field a
premise. No law of theirs is typed here.
OBJECT: `Sound.ArmCellIn` (Johnson/Desc/Sound/StatedCellIn.lean): at each entry of an array of the
second commitment that a linear form of a run names, the committed cell, read behind the commitment,
is the kind's stated function at the verifier's state in front.
USER: Johnson/Desc/K1/Law/ArmAtReads.lean (the binder hArm of K01_law's fifty later places).
LETTERS: Rd own own' piece run s a b rd (ArmCellIn's own); the kinds' letters under their own names.
  `LayLeft`          the ten premises of `OnBytes.Road.K4.armCell_lay`
                   (Johnson/Road/K4/ArmLay.lean), to the letter: hs ho hA hE T hfun htab hu3 hAc hM
  `armCellIn_lay`    **the call**: LayLeft gives ArmCellIn at K4's function `uLay tl M`
  `AttLeft`          the eleven premises of `First.Att.P.armCellIn_att`
                   (Johnson/Desc/First/Att/ArmAtt.lean), to the letter: hA hin hNM hW hE T hfun htab
                   hu3 hAc hM
  `armCellIn_att'`   **the call**: AttLeft gives ArmCellIn at K5's function
                   `uArm W (linkNo s)`
  `LayOwes`, `AttOwes`   the same less T and hAc (eight fields, nine fields): `LayOwes.left`,
                   `AttOwes.left` make LayLeft | AttLeft of them, the tie and the cells' equation
  `LayRest`, `AttRest`   what is left when the facts of the step at the reads are paid too
                   (Johnson/Desc/K1/Law/ArmStep.lean): three fields (hE hu3 hM), eight fields (hA hin hNM
                   hW hE htab hu3 hM; htab and hu3 now speak of the state's parameters IN FRONT)
  `oneEntry e`, `NamedEntry`, `armCellIn_of_entries`   AN ENTRY AT A TIME: ArmCellIn at a reader follows
                   from ArmCellIn at the reader that answers one form with the one entry e, for each
                   entry e of the second commitment that a form of the run names: so a kind's premise
                   "every entry that a form names ..." is asked at such an e alone (`oneEntry_all`)
  `armCellIn_not_both`   WHY THE TIE MUST BE ASKED AT THE WITNESS: two tables of messages that agree on
                   the first commitment's seats and part at a cell of the second commitment that a
                   form names cannot both meet ArmCellIn, whatever the stated function
WHOSE EACH FIELD IS: the two files' own heads say it, premise by premise.
IS IT EMPTY HERE? NO MEMBER OF EITHER STRUCTURE IS SHOWN. Two rules over letters.
The output head's half
(Johnson/Desc/Kinds/Law/FourRunsTie.lean: armCellIn_K6_at_table)
is not called here: that file is not imported.
What is not claimed. Any field. Nothing on soundness.

-/
import Johnson.Road.K4.ArmLay
import Johnson.Desc.First.Att.ArmAtt
import Johnson.Desc.Sound.StatedCellIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

/-! ## 1 The feed-forward segments' -/

section
open OnBytes OnBytes.Model OnBytes.Road OnBytes.Road.K4
open OnBytes.Model.Layer (Own)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open VerifiableInference.Desc.First (S LayOwn)
open VerifiableInference.Desc.First.K8 (TieOf)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.K9L (Bound)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ ArmCell ArmCellIn)
open Meaning.Reads (cellA)

/-- **What `armCell_lay` still asks**, a field a premise. -/
structure LayLeft (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (tl tl' : HTailF2)
    (M : S → Bound GQ → Mats GQ) (b₀ : LayOwn) (o : Own) (n : ℕ) (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    Prop where
  hs : s.here = .lay b₀
  ho : b₀.own = some o
  hA : a.L = b₀.L
  hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
      x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n ∧
        ∃ y : HFun × ℕ × ℕ, y.1 ∈ o.funs ∧ tl.tabAt y.1 y.2.1 y.2.2 = some x.idx
  T : TieOf tl' A
  hfun : tl'.funs = o.funs
  htab : ∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg
  hu3 : u3Of tl' = o.v.iU3
  hAc : ∀ c, b₀.L.arrayOf[o.v.iU3]? = some c → ∀ i, i < n →
      A o.v.iU3 0 i = (dataQ own' b rd).cell c.1 c.2 0 i
  hM : InRange tl' (M s (dataQ own a rd)) (cellA tl' A)

/-- **The feed-forward kind's (K4's) half, called.** -/
theorem armCellIn_lay {Rd : Readers} {own own' : List (ℕ × ℕ)} {piece : ℕ} {run : String} {s : S}
    {a b : VerifiableInference.Desc.K9.Part} {rd : ℕ × ℕ → MsgQ} {tl tl' : HTailF2}
    {M : S → Bound GQ → Mats GQ} {b₀ : LayOwn} {o : Own} {n : ℕ} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (h : LayLeft Rd own own' piece run s a b rd tl tl' M b₀ o n A) :
    ArmCellIn Rd own own' piece run s a b rd (uLay tl M) :=
  fun R hR f hf x hx _ c hc h2 =>
    armCell_lay Rd own own' piece run a b rd h.hs h.ho h.hA h.hE h.T h.hfun h.htab h.hu3 h.hAc h.hM
      R hR f hf x hx c hc h2

/-- LayLeft less the tie (T) and the cells' equation (hAc). -/
structure LayOwes (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (a : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (tl tl' : HTailF2)
    (M : S → Bound GQ → Mats GQ) (b₀ : LayOwn) (o : Own) (n : ℕ) (A : ℕ → ℕ → ℕ → Cb.Gl.E) :
    Prop where
  hs : s.here = .lay b₀
  ho : b₀.own = some o
  hA : a.L = b₀.L
  hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
      x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n ∧
        ∃ y : HFun × ℕ × ℕ, y.1 ∈ o.funs ∧ tl.tabAt y.1 y.2.1 y.2.2 = some x.idx
  hfun : tl'.funs = o.funs
  htab : ∀ Fn c sg, tl.tabAt Fn c sg = tl'.tabAt Fn c sg
  hu3 : u3Of tl' = o.v.iU3
  hM : InRange tl' (M s (dataQ own a rd)) (cellA tl' A)

theorem LayOwes.left {Rd : Readers} {own : List (ℕ × ℕ)} {piece : ℕ} {run : String} {s : S}
    {a : VerifiableInference.Desc.K9.Part} {rd : ℕ × ℕ → MsgQ} {tl tl' : HTailF2}
    {M : S → Bound GQ → Mats GQ} {b₀ : LayOwn} {o : Own} {n : ℕ} {A : ℕ → ℕ → ℕ → Cb.Gl.E}
    (h : LayOwes Rd own piece run s a rd tl tl' M b₀ o n A) (own' : List (ℕ × ℕ))
    (b : VerifiableInference.Desc.K9.Part) (T : TieOf tl' A)
    (hAc : ∀ c, b₀.L.arrayOf[o.v.iU3]? = some c → ∀ i, i < n →
      A o.v.iU3 0 i = (dataQ own' b rd).cell c.1 c.2 0 i) :
    LayLeft Rd own own' piece run s a b rd tl tl' M b₀ o n A :=
  ⟨h.hs, h.ho, h.hA, h.hE, T, h.hfun, h.htab, h.hu3, hAc, h.hM⟩

/-- LayOwes less what the step at the reads itself gives: tl is the plan's. -/
structure LayRest (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (a : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (tl tl' : HTailF2)
    (M : S → Bound GQ → Mats GQ) (o : Own) (n : ℕ) (A : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop where
  hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, ∀ x ∈ f.ents.toList,
      x.tree = o.v.iU3 ∧ x.row = 0 ∧ x.idx < n ∧
        ∃ y : HFun × ℕ × ℕ, y.1 ∈ o.funs ∧ tl.tabAt y.1 y.2.1 y.2.2 = some x.idx
  hu3 : u3Of tl = o.v.iU3
  hM : InRange tl' (M s (dataQ own a rd)) (cellA tl' A)

end

/-! ## 2 The attention segments' -/

section
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (GQ MsgQ dataQ linkNo ArmCellIn)
open VerifiableInference.Desc.First.K8 (TieOf)
open OnBytes.Tie.Pv.Tail.Port (u3Of)
open K5Law (funsAt Cov)

/-- **What `armCellIn_att` still asks**, a field a premise. -/
structure AttLeft (W : Verify.Public) (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s : First.S) (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ)
    (A : Attention.Plan) (i : Runs.In) (tl' : HTailF2) (Ac : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop where
  hA : W.A[linkNo s / 2]? = some A
  hin : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, plannedK A)
  hNM : A.seam.tl.NM = A.seam.tl.mats.size
  hW : A.nW ≤ plannedK A
  hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, Cov A.iU3 (plannedK A) A.nW f
  T : TieOf tl' Ac
  hfun : tl'.funs.toList = funsAt A s
  htab : ∀ Fn c sg, A.seam.tl.tabAt Fn c sg = tl'.tabAt Fn c sg
  hu3 : u3Of tl' = A.iU3
  hAc : ∀ c, a.L.arrayOf[A.iU3]? = some c → ∀ i, i < A.nW →
      Ac A.iU3 0 i = (dataQ own' b rd).cell c.1 c.2 0 i
  hM : ∀ aI : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k → ∀ i, i < (tl'.mats.getD μ {}).m →
        |aI μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) →
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          Ac (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m => aI μ i c) i' : ℤ) :
              Cb.Gl.E)) →
      ∀ μ r c, μ < tl'.NM → r < (tl'.mats.getD μ {}).m → c < (tl'.mats.getD μ {}).k →
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) (dataQ own a rd) μ r c =
          ((aI μ r c : ℤ) : Cb.Gl.E)

/-- **Attention's (K5's) half, called.** -/
theorem armCellIn_att' {W : Verify.Public} {Rd : Readers} {own own' : List (ℕ × ℕ)} {piece : ℕ}
    {run : String} {s : First.S} {a b : VerifiableInference.Desc.K9.Part} {rd : ℕ × ℕ → MsgQ}
    {A : Attention.Plan} {i : Runs.In} {tl' : HTailF2} {Ac : ℕ → ℕ → ℕ → Cb.Gl.E}
    (h : AttLeft W Rd own own' piece run s a b rd A i tl' Ac) :
    ArmCellIn Rd own own' piece run s a b rd (uArm W (linkNo s)) :=
  armCellIn_att Rd own own' piece run rd h.hA h.hin h.hNM h.hW h.hE h.T h.hfun h.htab h.hu3 h.hAc
    h.hM

/-- AttLeft less the tie (T) and the cells' equation (hAc). -/
structure AttOwes (W : Verify.Public) (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s : First.S) (a : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ)
    (A : Attention.Plan) (i : Runs.In) (tl' : HTailF2) (Ac : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop where
  hA : W.A[linkNo s / 2]? = some A
  hin : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, plannedK A)
  hNM : A.seam.tl.NM = A.seam.tl.mats.size
  hW : A.nW ≤ plannedK A
  hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, Cov A.iU3 (plannedK A) A.nW f
  hfun : tl'.funs.toList = funsAt A s
  htab : ∀ Fn c sg, A.seam.tl.tabAt Fn c sg = tl'.tabAt Fn c sg
  hu3 : u3Of tl' = A.iU3
  hM : ∀ aI : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k → ∀ i, i < (tl'.mats.getD μ {}).m →
        |aI μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) →
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          Ac (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m => aI μ i c) i' : ℤ) :
              Cb.Gl.E)) →
      ∀ μ r c, μ < tl'.NM → r < (tl'.mats.getD μ {}).m → c < (tl'.mats.getD μ {}).k →
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) (dataQ own a rd) μ r c =
          ((aI μ r c : ℤ) : Cb.Gl.E)

theorem AttOwes.left {W : Verify.Public} {Rd : Readers} {own : List (ℕ × ℕ)} {piece : ℕ}
    {run : String} {s : First.S} {a : VerifiableInference.Desc.K9.Part} {rd : ℕ × ℕ → MsgQ}
    {A : Attention.Plan} {i : Runs.In} {tl' : HTailF2} {Ac : ℕ → ℕ → ℕ → Cb.Gl.E}
    (h : AttOwes W Rd own piece run s a rd A i tl' Ac) (own' : List (ℕ × ℕ))
    (b : VerifiableInference.Desc.K9.Part) (T : TieOf tl' Ac)
    (hAc : ∀ c, a.L.arrayOf[A.iU3]? = some c → ∀ i, i < A.nW →
      Ac A.iU3 0 i = (dataQ own' b rd).cell c.1 c.2 0 i) :
    AttLeft W Rd own own' piece run s a b rd A i tl' Ac :=
  ⟨h.hA, h.hin, h.hNM, h.hW, h.hE, T, h.hfun, h.htab, h.hu3, hAc, h.hM⟩

/-- AttOwes less what the step at the reads itself gives: l is the open link's number, tlF the
state's parameters in front. -/
structure AttRest (W : Verify.Public) (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ)
    (run : String) (s : First.S) (a : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (l : ℕ)
    (A : Attention.Plan) (i : Runs.In) (tlF tl' : HTailF2) (Ac : ℕ → ℕ → ℕ → Cb.Gl.E) : Prop where
  hA : W.A[l / 2]? = some A
  hin : inOf (seatCO (parCOf A)) (parCOf A) s = some (i, plannedK A)
  hNM : A.seam.tl.NM = A.seam.tl.mats.size
  hW : A.nW ≤ plannedK A
  hE : ∀ R, Rd.forms piece run s = some R → ∀ f ∈ R.forms, Cov A.iU3 (plannedK A) A.nW f
  htab : ∀ Fn c sg, A.seam.tl.tabAt Fn c sg = tlF.tabAt Fn c sg
  hu3 : u3Of tlF = A.iU3
  hM : ∀ aI : ℕ → ℕ → ℕ → ℤ,
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k → ∀ i, i < (tl'.mats.getD μ {}).m →
        |aI μ i c| < 2 * ((2 ^ lbz : ℕ) : ℤ)) →
      (∀ μ, μ < tl'.NM → ∀ c, c < (tl'.mats.getD μ {}).k →
        ∀ i', i' < Alg.symRows (tl'.mats.getD μ {}).m →
          Ac (tl'.gtTree.getD μ 0) i' c =
            ((Alg.pack ((radb : ℕ) : ℤ) (fun i : Fin (tl'.mats.getD μ {}).m => aI μ i c) i' : ℤ) :
              Cb.Gl.E)) →
      ∀ μ r c, μ < tl'.NM → r < (tl'.mats.getD μ {}).m → c < (tl'.mats.getD μ {}).k →
        matsOfData A.seam.tl ((s.link?.map (·.arrayOf)).getD #[]) (dataQ own a rd) μ r c =
          ((aI μ r c : ℤ) : Cb.Gl.E)

end

/-! ## 3 An entry at a time -/

section
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Readers Read entInT)
open VerifiableInference.Desc.Sound (MsgQ UFn second ArmCellIn)

/-- The reader that answers, everywhere, one form with the one entry e. -/
def oneEntry (e : OnBytes.Model.Ent) : Readers := ⟨fun _ _ _ => some ⟨[{ ents := #[e] }], []⟩⟩

/-- What holds of e holds of every entry that a form of `oneEntry e` names. -/
theorem oneEntry_all {P : OnBytes.Model.Ent → Prop} {e : OnBytes.Model.Ent} (h : P e) (piece : ℕ)
    (run : String) (s : S) : ∀ R, (oneEntry e).forms piece run s = some R → ∀ f ∈ R.forms,
      ∀ x ∈ f.ents.toList, P x := by
  intro R hR f hf x hx
  obtain rfl : (⟨[{ ents := #[e] }], []⟩ : Read) = R := Option.some.inj hR
  obtain rfl := List.mem_singleton.1 hf
  obtain rfl : x = e := by simpa using hx
  exact h

/-- e is an entry of an array cc of the second commitment that a form of the run names, and it passes
the public test. -/
def NamedEntry (Rd : Readers) (own : List (ℕ × ℕ)) (piece : ℕ) (run : String) (s : S)
    (a : VerifiableInference.Desc.K9.Part) (e : OnBytes.Model.Ent) (cc : ℕ × String) : Prop :=
  ∃ R f, Rd.forms piece run s = some R ∧ f ∈ R.forms ∧ e ∈ f.ents.toList ∧
    entInT own a e = true ∧ a.L.arrayOf[e.tree]? = some cc ∧ second s cc = true

/-- **An entry at a time.** -/
theorem armCellIn_of_entries (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (s : S) (a b : VerifiableInference.Desc.K9.Part) (rd : ℕ × ℕ → MsgQ) (u : UFn)
    (h : ∀ e cc, NamedEntry Rd own piece run s a e cc →
      ArmCellIn (oneEntry e) own own' piece run s a b rd u) :
    ArmCellIn Rd own own' piece run s a b rd u :=
  fun R hR f hf x hx hin c hc h2 =>
    h x c ⟨R, f, hR, hf, hx, hin, hc, h2⟩ _ rfl _ (List.mem_singleton.2 rfl) x (by simp) hin c hc h2

end

/-! ## 4 Why the tie must be asked at the witness -/

section
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (Readers Read entInT)
open VerifiableInference.Desc.Sound (MsgQ UFn dataQ dataQ_congr second ArmCellIn)

/-- **Two tables of messages that agree on the first commitment's seats and part at a cell of the
second commitment that a form names cannot both meet ArmCellIn**, whatever the stated function u. -/
theorem armCellIn_not_both (Rd : Readers) (own own' : List (ℕ × ℕ)) (piece : ℕ) (run : String)
    (s : S) (a b : VerifiableInference.Desc.K9.Part) (u : UFn) (rd rd' : ℕ × ℕ → MsgQ)
    (hag : ∀ z ∈ own, rd z = rd' z) (R : Read) (hR : Rd.forms piece run s = some R) (f : OnBytes.Model.Aff)
    (hf : f ∈ R.forms) (x : OnBytes.Model.Ent) (hx : x ∈ f.ents.toList) (hin : entInT own a x = true)
    (c : ℕ × String) (hc : a.L.arrayOf[x.tree]? = some c) (h2 : second s c = true)
    (hne : (dataQ own' b rd).cell c.1 c.2 x.row x.idx ≠ (dataQ own' b rd').cell c.1 c.2 x.row x.idx) :
    ¬ (ArmCellIn Rd own own' piece run s a b rd u ∧ ArmCellIn Rd own own' piece run s a b rd' u) := by
  rintro ⟨h, h'⟩
  apply hne
  rw [h R hR f hf x hx hin c hc h2, h' R hR f hf x hx hin c hc h2, dataQ_congr own a rd rd' hag]

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.armCellIn_lay
#print axioms VerifiableInference.Desc.K1.armCellIn_att'
#print axioms VerifiableInference.Desc.K1.LayOwes.left
#print axioms VerifiableInference.Desc.K1.AttOwes.left
#print axioms VerifiableInference.Desc.K1.oneEntry_all
#print axioms VerifiableInference.Desc.K1.armCellIn_of_entries
#print axioms VerifiableInference.Desc.K1.armCellIn_not_both
