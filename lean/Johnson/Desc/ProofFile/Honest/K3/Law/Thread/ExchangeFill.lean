-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeFill.lean: the honest side of the kind "lookup"
(K3): the two premises of `worth_site` (Honest/K3/Law/Thread/ExchangeSite.lean) on the site's data's
keys and bits, FROM SENTENCES ON A FILLING'S OWN KEYS AND BITS in the library's field. Theorems with
proofs; no definition.

The site's data are made of a structure of the program's elements that the seat's reader makes of
the input. A filling (`LookIn`, Honest/K3/Wit.lean) has its keys and bits in the library's field,
and that structure is its `hidden`. Sentences on fillings speak of `L.key` and `L.bit`.

  `key_of_lookIn`, `bits_of_lookIn`   the data's keys and bits at `L.hidden` are L's, the bits at
                     the planes that count
  `worth_site_fill`  `worth_site`, CONDITIONAL ON: the seat's reader yields `L.hidden` at the
                     challenges heard in front; L's keys are the joint vector of Kv w; L's bits are
                     nu w's readings of their places; and what `worth_site` asks besides

Who can pay the two sentences on L: Honest/K3/Law/MeetsNamed.lean has them for the four sorts of
filling, at named key vectors and at named readings with any mask row. They are not called here.

Limits. That the table of joints' own reading and key vectors at an honest witness are those named
ones is shown nowhere here. No instance of these hypotheses is exhibited in this file.
Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeSite
import Johnson.Desc.ProofFile.Honest.K3.WitLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E)
open OnBytes.Model (Fork)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K3 (faceOf)
open VerifiableInference.Desc.First.Look (planesOk)
open VerifiableInference.OnPublicFiles (K3Objects K3WorthPlanes K3WorthKeys)

local notation "FS" => VerifiableInference.Desc.First.S

/-- The data's keys at a filling's structure are the filling's. -/
theorem key_of_lookIn {P : Type} (N : KE → TwV.Nums P KE) (L : LookIn) (p : Pts) (x : Nat) :
    (dataAt N L.hidden p).key x = L.key (up p.theta) x :=
  hidden_key L p.theta 0 x

/-- The data's bits at a filling's structure are the filling's, at the planes that count. -/
theorem bits_of_lookIn {P : Type} (N : KE → TwV.Nums P KE) (L : LookIn) (p : Pts) (u j : Nat)
    (hj : j < (N (up p.theta)).n + 2) : (dataAt N L.hidden p).bits u j = L.bit u j :=
  (if_pos hj).trans (hidden_bit L u j)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Wt : Type}

/-- **CONDITIONAL, as the file's head lists: `worth_site` from sentences on a filling's own keys and
bits.** No instance of these hypotheses is exhibited in this file. -/
theorem worth_site_fill (chain : Nat) (k : Coins Bk) (blk : Block FS ProofFile.Cl) (Z : Pub) (s : Site)
    (J : LookJobs Ask) (wit : Local W₀ Rc Xi Tr → Ask) (st st' : FS)
    (m : Mid (Local W₀ Rc Xi Tr) Xo) (ds : List Fmt.Drawn)
    (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn)
    (hA : AtThr.LeftAt chain k blk Z s J wit st st' m ds y cols)
    (hf : s.at_.face = faceOf s.shape)
    (hLed : ∀ F, (seatOf K3Lot.ofForm s.digits).fork st = some F →
      LedgerIn s.at_.face s.p.first F)
    (hok : FoNums.ok s.shape = true) (hpo : planesOk s.shape s.p.lm = true)
    (nu : Wt → _root_.Fo.Pl → GE) (Kv : Wt → Nat → Nat → GE) (w : Wt)
    (h0 : nu w .zero = 0) (L : LookIn) (hw : wit m.st.input m.st.heard = L.hidden)
    (hK : ∀ x, x < 2 ^ s.shape.v →
      L.key (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) x =
        OnBytes.Ends.jointKey s.shape (Kv w)
          (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) x)
    (hB : ∀ u j, u < 2 ^ s.shape.d → j < 32 → L.bit u j =
      nu w ((_root_.Fo.numsF s.shape s.p.lm s.p.first
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta)).bAt u j))
    (hD : ∀ (c : RowCoins (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit
        s.at_).parts) (c' : (t : Stage) → StageCoins s.at_ t),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) blk.place
        (proverSideOfLookupInChainAtOneOwner (V₁ := Local W₀ Rc Xi Tr) (X₁ := Xo) ⟨ptsOf, pointsAt⟩ J wit s.at_).parts 0 =
          .ok c →
      CoinsAre (V := Unit) (courseAt s.at_ J s.p.first wit m ds c')
        (unlift (X := Xo) (fun (_ : Local W₀ Rc Xi Tr) => ()) wit
          (lookRow ⟨ptsOf, pointsAt⟩ J s.at_) c) →
      Dict (courseAt s.at_ J s.p.first wit m ds c') (nu w)) :
    K3Objects (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard s.shape
        s.p.lm s.p.first nu st' w ∧
      K3WorthPlanes (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard
        s.shape s.p.lm s.p.first nu st' w ∧
      K3WorthKeys (seatOf K3Lot.ofForm s.digits).fork (seatOf K3Lot.ofForm s.digits).heard
        s.shape s.p.lm s.p.first nu Kv st' w :=
  worth_site chain k blk Z s J wit st st' m ds y cols hA hf hLed hok hpo nu Kv w h0
    (fun u j hu hj => by
      show (dataAt _ (wit m.st.input m.st.heard) _).bits u j = _
      have hj' : j < 32 := hj
      rw [hw, bits_of_lookIn _ L _ u j hj']
      exact hB u j hu hj')
    (fun x hx => by
      show (dataAt _ (wit m.st.input m.st.heard) _).key x = _
      rw [hw, key_of_lookIn]
      exact hK x hx)
    hD

#print axioms ProofFile.Honest.K3.Law.Exchange.key_of_lookIn
#print axioms ProofFile.Honest.K3.Law.Exchange.bits_of_lookIn
#print axioms ProofFile.Honest.K3.Law.Exchange.worth_site_fill

end ProofFile.Honest.K3.Law.Exchange
