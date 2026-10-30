-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Door/Law/K5LeftFitsG.lean: kind K5: THE CLAUSE "planes" OF K5FillIns (Att/K05Closes.lean: all that the kind's row of the table opens, at the verifier's state after the kind's sub-protocol, gives the item worth m 2 "planes" in front of it) AS A THEOREM AT THE COMMON LETTERS
of K5Left's assembly.
THE ROAD: the open item formsT m 2 "planes" gives its sentence (hfT_plus, Door/Law/K5GainsPlus.lean) · worthPlanes_behind (Att/K05PlanesBack.lean: K05_host_planes_door called, the run's yes drawn from the sentence itself) · hW_planes (K5GainsPlus.lean: the filling's equation at the item).
Main name: planes_plus: it concludes the clause's own text: the premise hPl of ins_plus (Door/Law/K5LeftFitsB.lean): planes_fits hands it in: Lean's own check.
OF THE VERIFIER's STATE TWO PREMISES STAY, both under the table's promise in front: hH5 (nothing of the kind's own was received yet: the first clause of the public item callerIn m) · hBare (the start form of the leaves' sumcheck is bare: the lookup argument's files' to show).
IS IT EMPTY HERE? An implication.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5LeftFitsB
import Johnson.Desc.First.Att.Door.Law.K5GainsPlus
import Johnson.Desc.First.Att.K05PlanesBack
import Johnson.Desc.First.Att.K05StatedArm

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open Cb Cb.Fo Cb.LdLkp OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Maker Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Sent attSg JAtt enMask lookAt placeAt k3SortAt)
open VerifiableInference.Desc.First.FillK4 (isLay)
open VerifiableInference.Desc.K9 (RunOf readerOf)
open VerifiableInference.Desc.K13.Law (DataK13 fillK13)
open VerifiableInference.OnPublicFiles (k3LeftItemAt k3LeftOnItemAt)
open VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.Desc.First.Look (bornAt keptAt sigListCalls)
open VerifiableInference.Desc.K9 (statesOfLink readersOfLink LinkHoles)

section
variable {Pp Cells Tok Cl : Type} {nR : ℕ} {Fr : Frame}
  (Mg Mg0 : Meaning Pp (Wit Cells Tok MsgT)) (D : PubData)
  (cs : OnBytes.Codes)
  (smp : Pp × S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Pp × S → Option Cells) (in0 : Pp × S → Bool)
  (D13 : DataK13 Pp (Wit Cells Tok MsgT) nR)
  (bs : ℕ) (claim : Aff → Cl) (Wv : Verify.Public) (g : ℕ) (before : List (ℕ × ℕ)) (a : Attention.Plan) (x : Look.Place)
  (Dn : Sent) (rad : OracleShape → Nat) (Ex : Iop.ExtSpec) (Wp : Type)
  (α : TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl)) → Cb.Gl.E) (plJ : ℕ → ℕ → JAtt x.ns a.seam.tl)
  (I : PinItemP Fr seatSO bs (Wit Cells Tok MsgT) (attSg x Dn rad).Msg)
  (R' : Pp → S × Fr.E.Str → Wit Cells Tok MsgT → Prop)
  (links : List ModelPart) (pl : VerifiableInference.Desc.Place) (O : List Item) (Q : List Pub) (states : ℕ → List (RunOf S))

include Ex Wp α in
theorem planes_plus {wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (uL uH : ℕ → UFn)
    (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
    (Gn : MgGains Mg Dn.codes arr ms D.Rd D.runs (Stated.of (uBySort uL (uArm Wv) uH)) D.N wt (2 * g + 1) x a.S a.seam.tl Dn rad seat arr)
    (hxl : x.link = 2 * g + 1) (hfs : x.fs = a.fs) (hxlm : x.lm = a.S.cf.lmb) (hok : FoNums.ok x.fs = true)
    (hA : Wv.A[x.link / 2]? = some a) (hOP : K5Law.OfPlan a) (hPos : K5Law.PosG (parCOf a).geo)
    (H : LinkHoles) (Lk : Link S Claim) (hRd : D.Rd x.link = readersOfLink H Lk) (hsil : ∀ s, H.silent 1 "planes" s = none)
    {same : S → S → Bool} (claimC : Aff → Claim) (hcl : ∀ f, (claimC f).form = f) {nm : String}
    (hL : ((statesOfLink Lk 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, K3.planesRun (K3.seatCalls claimC) a.S.cf.lmb (readersOfO a))))
    (hrP : D.runs x.link 2 "planes" = [(1, "planes")])
    (hRet : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn a s att hd G)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q) {hi : ℕ}
    (hdoor : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' →
      DoorYes Wv x Dn (bornAt Dn x.link) (keptAt Dn x.link).length (D.N.sent x.link 0)
        (psOf (sigListCalls Dn rad x.link) seat (readMsgs Dn x a.seam.tl)) (qsOf (sigListCalls Dn rad x.link) (readMsgs Dn x a.seam.tl)) hi
        ((gOf π) a') a'.1)
    (hpub : TiePub Dn x a.seam.tl hi rad) (hhi : hi ≤ x.ns)
    (hmem : ∀ (fs : List Aff) (k : Fin (sigListCalls Dn rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) Dn x.link k.val → MemAt ms (sigListCalls Dn rad x.link) seat k)
    (hn : x.fs.NC * 2 ^ (x.fs.kT + 5 - a.S.cf.lmb) ≤
      (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k * ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb))
    (hH5 : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → att.heard5 = none)
    (hBare : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → OnBytes.Road.Rows.Bare ((gOf π) (s, y)).leaves.start) :
    ∀ π : Pp, ∀ s att hd G rs y y' w, onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → SameBelow Fr bs y y' →
      (∀ i ∈ [Item.formsT (2 * g + 1) 3 "own", .formsT (2 * g + 1) 2 "planes", .formsT (2 * g + 1) 2 "join", .pin (2 * g + 1) 0, .pinW,
          .constr (2 * g + 1) .small], i.holds D.N Mg (π, behind s att hd G) (strsOf Fr y') w) →
      Mg.worth (2 * g + 1) 2 "planes" (π, s) (strsOf Fr y) w := by
  intro π s att hd G rs y y' w hon hm e hh _ hopen
  have Fa := frontAll_of_door hA hOP (hdoor π (s, y) ⟨hon, hm⟩)
  obtain ⟨i, K, _, _, _, _, _, _, hin, _⟩ := hRet π s y att hd G rs hon hm e hh
  have hLf := hLI π (s, y) (onAt_pubP hon hm _ hleftQ)
  have hshape : ((gOf π) (s, y)).shape = x.fs := by
    obtain ⟨_, _, _, _, _, Lf, _, _, _⟩ := hLf
    exact Lf.shape
  obtain ⟨_, _, _, _, hd', _⟩ := left_parts hLf
  have hlk : att.lookHeard = some ((gOf π) (s, y)) := by
    have := hd'
    unfold K3.seatCalls S.lookHeard? at this
    simp only [e] at this
    exact this
  have hit : Mg.formsT x.link 2 "planes" (π, behind s att hd G) (strsOf Fr y') w := by
    rw [hxl]
    exact hopen (.formsT (2 * g + 1) 2 "planes") (by simp)
  have hWp := worthPlanes_behind x a Dn rad Ex Wp α hOP hPos H Lk claimC hcl hL e hm (hH5 π s y att hon hm e) hh (hsil _) hin hlk
    (hshape.trans hfs) (by rw [hshape]; exact hok) (hBare π s y att hon hm e) (by rw [hshape]; exact hn) x.F.next a.ns
    (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs)) D.Rd hRd D.runs (Stated.of (uBySort uL (uArm Wv) uH)) D.N arr seat
    ms hi Fa hpub hhi (w := w) (hfT_plus Gn x.link 2 "planes" (π, behind s att hd G) (strsOf Fr y') w hit) (by rw [hrP]; simp) hmem
    (fun s a₀ h hl => hSt_of_arm hA uL uH s a₀ h hl)
  rw [hshape, ← hxlm] at hWp
  exact hW_planes Gn claimC π s (strsOf Fr y) w hWp

/-- Lean's own check that planes_plus' conclusion is the clause's type. -/
theorem planes_fits {wt : ℕ → Pp × S → Strs → Wit Cells Tok MsgT → Prop} (arr : ℕ → ℕ → ℕ) (ms : List Mem) (uL uH : ℕ → UFn)
    (seat : Fin (sigListCalls Dn rad x.link).length → ℕ × ℕ)
    (Gn : MgGains Mg Dn.codes arr ms D.Rd D.runs (Stated.of (uBySort uL (uArm Wv) uH)) D.N wt (2 * g + 1) x a.S a.seam.tl Dn rad seat arr)
    (hxl : x.link = 2 * g + 1) (hfs : x.fs = a.fs) (hxlm : x.lm = a.S.cf.lmb) (hok : FoNums.ok x.fs = true)
    (hA : Wv.A[x.link / 2]? = some a) (hOP : K5Law.OfPlan a) (hPos : K5Law.PosG (parCOf a).geo)
    (H : LinkHoles) (Lk : Link S Claim) (hRd : D.Rd x.link = readersOfLink H Lk) (hsil : ∀ s, H.silent 1 "planes" s = none)
    {same : S → S → Bool} (claimC : Aff → Claim) (hcl : ∀ f, (claimC f).form = f) {nm : String}
    (hL : ((statesOfLink Lk 1).find? fun c => c.1 == "planes") = some (guardC same
      (nm, K3.planesRun (K3.seatCalls claimC) a.S.cf.lmb (readersOfO a))))
    (hrP : D.runs x.link 2 "planes" = [(1, "planes")])
    (hRet : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn) (hd : Heard) (G : Fork) (rs : List Fmt.RoundView),
      onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none → s.here = .att att →
      hear (parO Wv (2 * g + 1) a before).own (att.F, rs, 0) = some (hd, G, [], 0) → RunsReturn a s att hd G)
    (x0 : Pp → S × Fr.E.Str → TX (Unit × Cb.Gl.E) Cb.Gl.E (Option (JAtt x.ns a.seam.tl))) (gOf : Pp → S × Fr.E.Str → Forest.Heard)
    (hLI : LeftIsP Mg claim Wv g before a x plJ x0 gOf) (hleftQ : Pub.left (2 * g + 1) ∈ Q) {hi : ℕ}
    (hdoor : ∀ (π : Pp) (a' : S × Fr.E.Str), onT D.N Mg links π Fr pl O Q a' →
      DoorYes Wv x Dn (bornAt Dn x.link) (keptAt Dn x.link).length (D.N.sent x.link 0)
        (psOf (sigListCalls Dn rad x.link) seat (readMsgs Dn x a.seam.tl)) (qsOf (sigListCalls Dn rad x.link) (readMsgs Dn x a.seam.tl)) hi
        ((gOf π) a') a'.1)
    (hpub : TiePub Dn x a.seam.tl hi rad) (hhi : hi ≤ x.ns)
    (hmem : ∀ (fs : List Aff) (k : Fin (sigListCalls Dn rad x.link).length),
      ReadMsg (ReadAddr a.seam.tl fs) Dn x.link k.val → MemAt ms (sigListCalls Dn rad x.link) seat k)
    (hn : x.fs.NC * 2 ^ (x.fs.kT + 5 - a.S.cf.lmb) ≤
      (a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).k * ((a.seam.tl.mats.getD (a.S.cf.NAs + 2) {}).m / 2 ^ a.S.cf.lmb))
    (hH5 : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → att.heard5 = none)
    (hBare : ∀ (π : Pp) (s : S) (y : Fr.E.Str) (att : AttOwn), onAt D.N Mg links (some pl) O Q (π, s) (strsOf Fr y) → s.failed = none →
      s.here = .att att → OnBytes.Road.Rows.Bare ((gOf π) (s, y)).leaves.start)
    (π : Pp) (Ins : K5FillIns Mg D.N links π Fr bs (2 * g + 1) pl O Q (parO Wv (2 * g + 1) a before).own x a.S a.seam.tl Dn rad Ex Wp α a.ns
      (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs)) (x0 π) I.part) :
    K5FillIns Mg D.N links π Fr bs (2 * g + 1) pl O Q (parO Wv (2 * g + 1) a before).own x a.S a.seam.tl Dn rad Ex Wp α a.ns
      (numsPlan (parO Wv (2 * g + 1) a before).own (x.F.next + Forest.elems x.fs)) (x0 π) I.part :=
  { Ins with
    planes := (planes_plus Mg D bs claim Wv g before a x Dn rad Ex Wp α plJ links pl O Q arr ms uL uH seat Gn hxl hfs hxlm hok hA hOP hPos H Lk hRd hsil
      claimC hcl hL hrP hRet x0 gOf hLI hleftQ hdoor hpub hhi hmem hn hH5 hBare π) }

end

end H2K5.Door

#print axioms H2K5.Door.planes_plus
#print axioms H2K5.Door.planes_fits
