-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/SortK3Objects.lean: WHAT IS LEFT OF A LINK's LAW (K9): THE FIELDS k3,
k3p, k3s, k3sL OF `SortRest` (SortRest.lean) AT THE ENTRIES "objects": PAID, IN THE
GOALS' SCOPE, AT THE PINNED LETTERS ψ := psiAll, φ := phiAll u psiAll. Definitions, and theorems:
calls. IT PAYS NO LAW OF ITS OWN.

THE TIE. What the description's own link number m states under "objects" at the lookup's block
(number IM.k3Ix m d: d: the digits' lookup, else the calls') IS the kind's own run at that seat, AS
A FUNCTION (`k03_objects_raw`, Johnson/Desc/First/Look/K03StatesRaw.lean): so `At L o run` pins
run:
  at_objects_is     At L (IM.k3Ix m d, "objects") run ⊢ run = objectsRun (seatOf K3Lot.ofForm d)
THE LETTERS, BY SEAT. hdAt d (hdDigits | hdCalls) · t3Obj | l3Obj lmC jC lmD jD d:
plainTm (objVals ..) | objLen .. at that seat's reader and two numbers · dOf o (6 ≤ o.1: the
digits' block is number 6 or 7, the calls' 1 or 2) · t3O | l3O .. o: the same as functions of the
entry.
THE FIELDS AT ONE ENTRY.
  k3_objects        **RunOk** .. run (t3Obj .. d) (l3Obj .. d): objects_runOk
                    (Johnson/Top/H/Keep/RunsPlain.lean), all six premises laid: UNDER ONE PREMISE
                    ON THE LETTER Ok: hK : ∀ q, Ok q → kxAll lmC jC lmD jD q
  k3p_objects · k3s_objects · k3sL_objects   by objects_puts | objects_core (Keep/RunsPutFork.lean)
THE ENTRIES. objects_entry_low (m ≠ 24: 1 | 6) · objects_entry_head (m = 24: 2 | 7) · dOf_k3Ix.
AT A LAYERS' LINK THE LIST OF ENTRIES HAS "objects" ALONE: SO THE FOUR FIELDS WHOLE, IN THE FIELDS'
OWN TEXTS: k3_layers · k3p_layers · k3s_layers · k3sL_layers.

PREMISES: hS hR O (the goals' scope and the maker's opening) · m < 25 · hL : c.links[m]? = some L ·
hK.
Limits. WHETHER Ok CAN BE HAD WITH kxAll INSIDE AT AN HONEST STATE IS NOT SHOWN HERE: where no fixed
part meets Ok, RunOk holds of nothing. The four numbers stay letters. NOTHING ON "planes" | "join" |
k3d | k3g | k3f | h4. NO MEMBER. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.SortLetters
import Johnson.Desc.First.Link.Law.SizedRides
import Johnson.Desc.First.Link.Law.HitemsStill
import Johnson.Desc.First.Link.Law.GoodFull
import Johnson.Desc.First.Look.K03StatesRaw
import Johnson.Top.H.Keep.SeatsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Block Chain Link FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (atS)
open VerifiableInference.Desc.K9L (RunOk plainTm Pub9 Fx9 O9 Bound)
open VerifiableInference.Desc.PhiAll
open VerifiableInference.Desc.LinkJoin (At FullAt HasFork Q)

/-! ## The tie -/

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **What the link states under "objects" at a lookup's block is the kind's own run at that
seat.** -/
theorem at_objects_is (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
    (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25) (d : Bool)
    {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L)
    {run : ℕ → S → Except String (List ProofFile.Cl × S)} (h : At L (IM.k3Ix m d, "objects") run) :
    run = objectsRun (seatOf K3Lot.ofForm d) := by
  obtain ⟨Lk, h1, h2⟩ := k03_objects_raw hS hR O m hm d
  obtain rfl : Lk = L := Option.some.inj (h1.symm.trans hL)
  obtain ⟨b, hb, hl⟩ := Option.bind_eq_some_iff.1 h
  have hb' : Lk.hear[IM.k3Ix m d]? = some b := hb
  have hl' : b.claims.lookup "objects" = some run := hl
  obtain ⟨x, hx, hx2⟩ := Desc.LinkJoin.find_of_lookup "objects" b.claims run hl'
  have e : Desc.K9.statesOfLink Lk (IM.k3Ix m d) = b.claims := by
    unfold Desc.K9.statesOfLink
    rw [hb']
    rfl
  rw [e, hx] at h2
  rw [← hx2]
  exact congrArg Prod.snd (Option.some.inj h2)

end

/-! ## The letters, by seat -/

/-- The reader of what was heard at the seat. -/
def hdAt (d : Bool) : Phi BetaAll → Option Forest.Heard := cond d hdDigits hdCalls

/-- The terms of "objects" at the seat. -/
def t3Obj (lmC jC lmD jD : ℕ) (d : Bool) : ℕ → Q BetaAll → Bound GE → List (ℕ × GE) :=
  plainTm (objVals (hdAt d) (cond d lmD lmC) (cond d jD jC))

/-- Their number. -/
def l3Obj (lmC jC lmD jD : ℕ) (d : Bool) : Q BetaAll → ℕ :=
  objLen (hdAt d) (cond d lmD lmC) (cond d jD jC)

theorem heard_at (u : HTailF2) (d : Bool) :
    ∀ s, (seatOf K3Lot.ofForm d).heard s = hdAt d (phiAll u psiAll s) := by
  intro s
  cases d
  · exact (hdCalls_all u s).symm
  · exact (hdDigits_all u s).symm

theorem fits_at (d : Bool) : SeatFits (seatOf K3Lot.ofForm d) (·.form) := by
  cases d
  · exact seatCalls_fitsP
  · exact seatDigits_fitsP

theorem k3Ok_at {Ok : Q BetaAll → Prop} {lmC jC lmD jD : ℕ}
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) (d : Bool) :
    ∀ q, Ok q → K3Ok (hdAt d) (cond d lmD lmC) (cond d jD jC) q := by
  cases d
  · exact fun q h => (hK q h).1
  · exact fun q h => (hK q h).2

/-! ## The four fields at one entry -/

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
  (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25)
  {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L)
include hS hR O hm hL

/-- **k3 at "objects".** -/
theorem k3_objects (d : Bool) (u : HTailF2) (Ok : Q BetaAll → Prop) (nU : Array ℕ)
    {lmC jC lmD jD : ℕ} (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q)
    (run : ℕ → S → Except String (List ProofFile.Cl × S)) (h : At L (IM.k3Ix m d, "objects") run) :
    RunOk Reading.gl atS (O9 (phiAll u psiAll) Ok (FullAt nU)) (Fx9 (phiAll u psiAll) Ok) run
      (t3Obj lmC jC lmD jD d) (l3Obj lmC jC lmD jD d) := by
  rw [at_objects_is hS hR O hm d hL h]
  exact objects_runOk (phiAll u psiAll) Ok (FullAt nU) (hdAt d) (cond d lmD lmC) (cond d jD jC)
    (seatOf K3Lot.ofForm d) (atS2_seatOf d) (fits_at d) (phiAll_putFork_all u) (heard_at u d)
    (k3Ok_at hK d)

/-- **k3p at "objects".** -/
theorem k3p_objects (d : Bool) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m d, "objects") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → ∃ G, e₁ = e.putFork G := by
  rw [at_objects_is hS hR O hm d hL h]
  exact objects_puts _ (atS2_seatOf d)

/-- **k3s at "objects".** -/
theorem k3s_objects (d : Bool) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m d, "objects") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork Sized e → HasFork Sized e₁ := by
  rw [at_objects_is hS hR O hm d hL h]
  rintro n e cl e₁ hr ⟨G₀, hF, hz⟩
  obtain ⟨G, rfl, _, _, hG⟩ := objects_core _ (atS2_seatOf d) n e cl e₁ G₀ hF hz hr
  exact ⟨G, Desc.LinkJoin.fork_putFork e G₀ hF G, hG⟩

/-- **k3sL at "objects".** -/
theorem k3sL_objects (d : Bool) (run : ℕ → S → Except String (List ProofFile.Cl × S))
    (h : At L (IM.k3Ix m d, "objects") run) :
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e →
      HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁ := by
  rw [at_objects_is hS hR O hm d hL h]
  rintro n e cl e₁ hr ⟨G₀, hF, hz, hn⟩
  obtain ⟨G, rfl, e1, e2, hG⟩ := objects_core _ (atS2_seatOf d) n e cl e₁ G₀ hF hz hr
  exact ⟨G, Desc.LinkJoin.fork_putFork e G₀ hF G, hG, by rw [e1, e2]; exact hn⟩

end

/-! ## The entries -/

/-- Which seat an entry "objects" stands at. -/
def dOf (o : ℕ × String) : Bool := decide (6 ≤ o.1)

theorem dOf_k3Ix (m : ℕ) (d : Bool) (n : String) : dOf (IM.k3Ix m d, n) = d := by
  unfold dOf
  cases d <;> by_cases e : m = 24 <;> simp [IM.k3Ix, e]

/-- The terms and their number, as functions of the entry. -/
def t3O (lmC jC lmD jD : ℕ) (o : ℕ × String) : ℕ → Q BetaAll → Bound GE → List (ℕ × GE) :=
  t3Obj lmC jC lmD jD (dOf o)

def l3O (lmC jC lmD jD : ℕ) (o : ℕ × String) : Q BetaAll → ℕ := l3Obj lmC jC lmD jD (dOf o)

theorem objects_entry_low {m : ℕ} (hm : m ≠ 24) {o : ℕ × String}
    (ho : o = (1, "objects") ∨ o = (6, "objects")) : ∃ d, o = (IM.k3Ix m d, "objects") := by
  rcases ho with rfl | rfl
  · exact ⟨false, by simp [IM.k3Ix, hm]⟩
  · exact ⟨true, by simp [IM.k3Ix, hm]⟩

theorem objects_entry_head {o : ℕ × String} (ho : o = (2, "objects") ∨ o = (7, "objects")) :
    ∃ d, o = (IM.k3Ix 24 d, "objects") := by
  rcases ho with rfl | rfl
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-! ## A layers' link: the four fields whole -/

section
variable {Pf : VerifierAndGoals.PublicFiles} {pp₀ : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  (hS : VerifierAndGoals.InScope Pf = true) (hR : VerifierAndGoals.readFiles Pf = .ok pp₀)
  (O : IM.Open OnBytes.secondHashFunction Pf.pol lay Pf.KL F Z Bs base c A B) {m : ℕ} (hm : m < 25)
  (h24 : m ≠ 24) {L : Link S ProofFile.Cl} (hL : c.links[m]? = some L)
include hS hR O hm h24 hL

theorem k3_layers (u : HTailF2) (Ok : Q BetaAll → Prop) (nU : Array ℕ) {lmC jC lmD jD : ℕ}
    (hK : ∀ q, Ok q → kxAll lmC jC lmD jD q) :
    ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
      RunOk Reading.gl atS (O9 (phiAll u psiAll) Ok (FullAt nU)) (Fx9 (phiAll u psiAll) Ok) run
        (t3O lmC jC lmD jD o) (l3O lmC jC lmD jD o) := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  unfold t3O l3O
  rw [dOf_k3Ix]
  exact k3_objects hS hR O hm hL d u Ok nU hK run h

theorem k3p_layers : ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → ∃ G, e₁ = e.putFork G := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  exact k3p_objects hS hR O hm hL d run h

theorem k3s_layers : ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork Sized e → HasFork Sized e₁ := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  exact k3s_objects hS hR O hm hL d run h

theorem k3sL_layers : ∀ o ∈ [((1 : ℕ), "objects"), (6, "objects")], ∀ run, At L o run →
    ∀ n e cl e₁, run n e = .ok (cl, e₁) → HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e →
      HasFork (fun F => Sized F ∧ F.LS.size = F.ns) e₁ := by
  intro o ho run h
  obtain ⟨d, rfl⟩ := objects_entry_low h24 (by simpa using ho)
  exact k3sL_objects hS hR O hm hL d run h

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.at_objects_is
#print axioms VerifiableInference.OnPublicFiles.heard_at
#print axioms VerifiableInference.OnPublicFiles.fits_at
#print axioms VerifiableInference.OnPublicFiles.k3Ok_at
#print axioms VerifiableInference.OnPublicFiles.k3_objects
#print axioms VerifiableInference.OnPublicFiles.k3p_objects
#print axioms VerifiableInference.OnPublicFiles.k3s_objects
#print axioms VerifiableInference.OnPublicFiles.k3sL_objects
#print axioms VerifiableInference.OnPublicFiles.dOf_k3Ix
#print axioms VerifiableInference.OnPublicFiles.objects_entry_low
#print axioms VerifiableInference.OnPublicFiles.objects_entry_head
#print axioms VerifiableInference.OnPublicFiles.k3_layers
#print axioms VerifiableInference.OnPublicFiles.k3p_layers
#print axioms VerifiableInference.OnPublicFiles.k3s_layers
#print axioms VerifiableInference.OnPublicFiles.k3sL_layers
