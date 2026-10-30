-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/DataAlong.lean: AT A DESCRIPTION WHOSE DATA RETURN, EVERY MAKER's PIECE
WHOSE BLOCK DECLARES K10's ROUNDS HAS THE DATA OF WHICH K10's LAW SPEAKS: BY THE RULE ON A
PIECE's STRETCH (Johnson/Desc/Sound/Stretch.lean). Statements and proofs.

Why. CutAtK10.lean (beside this file) gets the data of the maker's piece from the chain's written
rounds, with premises on these. Johnson/Desc/Sound/Stretch.lean says more directly: at
every description F with `F.data file = .ok D`, along every piece p of the maker's three rows, round
by round, the data are those of p's own block's declared rounds (`stretchOfData`: `Along (RoundIs
..) p.b.rounds p.ds`). `RoundIs` names five of a round's six fields outright and the number of the
trees that it sends: at a round that sends no root that is all six.
  `bat_of_is`, `eps_of_is`, `two_of_is`: data that are those of K10's declared round "BAT" (at work
    0), "FOLD epsilon", "FOLD round" ARE `dBat rows`, `dEps`, `dTwo` (CutAtK10.lean).
    `twos_of_along`, `ds_of_along`: so along the kind's declared rounds, at both numbers of proof of
    work 0 and at 2 + Q.k data.
  `piece_ds`: at any piece whose block declares these rounds, whatever its state.
    `k10_data_at_desc`: AT A DESCRIPTION: under `stretchOfData`'s own premises.
  `bare_is_on`: an equation between two pieces over the bare state: q over the pair (what was handed
    to the chain, the verifier's state), with these data and nothing put back: the piece with `below
    b`, q's base, data and errors AND THE EXTRACTOR THAT HANDS THE WITNESS ON is `pieceOn b`
    (AtAny.lean) at that extractor. THAT IS NOT THE PIECE AT WHICH K10's LAW CAN HOLD AT THE TABLE
    OF JOINTS' RELATIONS: K10's row of that table lays messages into the witness: its extractor is
    not the identity. The equation serves a sub-protocol that lays nothing. What K10 takes from this
    file is the data.
Limits. That the piece has 2 + Q.k data is a premise (the tiling's first count: as many as
the block declares, less what is put back). The two numbers of proof of work are premises. To carry
K10's law from a piece over the bare state to the lifted piece, WITH THE LAW's OWN EXTRACTOR, is not
here. That the description's data return is a premise. Nothing on soundness.



-/
import Johnson.Desc.First.Close.Law.CutAtK10
import Johnson.Desc.Sound.Stretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)
open _root_.Run (ckP)

theorem bat_of_is (num : Fmt.TreeSource → ℕ) (rows : ℕ) (d : RDT)
    (h : RoundIs num { entry := { name := "BAT", work := 0, drawE := 1, rows := rows } } d) :
    d = dBat rows := by
  rcases d with ⟨⟨en, kd, it, tr, op⟩, st⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at h1 h2 h3 h4 h5 h6
  have hk : Fmt.kindOf "BAT" = some .elems := by decide
  rw [hk] at h2
  obtain rfl := Option.some.inj h2
  obtain rfl : tr = [] := List.length_eq_zero_iff.1 h6
  subst h1 h3 h4 h5
  simp [dBat, dOf, rdtOf, Three.rdOf, Fmt.DeclaredRound.items, Fmt.Entry.cut, Fmt.M2.rBatN]

theorem eps_of_is (num : Fmt.TreeSource → ℕ) (d : RDT)
    (h : RoundIs num { entry := { name := "FOLD epsilon", work := 0, msg := 24, drawE := 1 } } d) :
    d = dEps := by
  rcases d with ⟨⟨en, kd, it, tr, op⟩, st⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at h1 h2 h3 h4 h5 h6
  have hk : Fmt.kindOf "FOLD epsilon" = some (Fmt.M1.rEps "FOLD epsilon").kind := by decide
  rw [hk] at h2
  obtain rfl := Option.some.inj h2
  obtain rfl : tr = [] := List.length_eq_zero_iff.1 h6
  subst h1 h3 h4 h5
  rfl

theorem two_of_is (num : Fmt.TreeSource → ℕ) (d : RDT)
    (h : RoundIs num { entry := { name := "FOLD round", work := 0, msg := 48, drawE := 1 } } d) :
    d = dTwo := by
  rcases d with ⟨⟨en, kd, it, tr, op⟩, st⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  simp only at h1 h2 h3 h4 h5 h6
  have hk : Fmt.kindOf "FOLD round" = some .elems := by decide
  rw [hk] at h2
  obtain rfl := Option.some.inj h2
  obtain rfl : tr = [] := List.length_eq_zero_iff.1 h6
  subst h1 h3 h4 h5
  rfl

/-- k rounds "FOLD round". -/
theorem twos_of_along (num : Fmt.TreeSource → ℕ) : ∀ (k : ℕ) (ds : List RDT),
    Along (RoundIs num) (List.replicate k
      ({ entry := { name := "FOLD round", work := 0, msg := 48, drawE := 1 } } : Fmt.DeclaredRound))
      ds → ds.length = k → ds = List.replicate k dTwo
  | 0, [], _, _ => rfl
  | 0, _ :: _, _, h => nomatch h
  | _ + 1, [], _, h => nomatch h
  | k + 1, d :: ds, h, hl => by
    rw [List.replicate_succ] at h ⊢
    rw [two_of_is num d h.1, twos_of_along num k ds h.2 (Nat.succ.inj hl)]

/-- **WHERE THE DATA ARE THOSE OF K10's DECLARED ROUNDS, ROUND BY ROUND, AND AS MANY, THEY ARE THE
LAW's.** -/
theorem ds_of_along {Cl : Type} (num : Fmt.TreeSource → ℕ) (Q : Par) (h1 : Q.workField = 0)
    (h2 : Q.workClose = 0) (ds : List RDT)
    (h : Along (RoundIs num) (kind (Cl := Cl) Q).rounds ds) (hl : ds.length = 2 + Q.k) :
    ds = dBat Q.rows :: dEps :: List.replicate Q.k dTwo := by
  have h' : Along (RoundIs num) ((entries Q).map fun x => ({ entry := x } : Fmt.DeclaredRound)) ds := h
  unfold entries at h'
  rw [h1, h2] at h'
  simp only [List.map_cons, List.map_replicate] at h'
  match ds, h', hl with
  | d0 :: d1 :: ds, h', hl =>
    rw [bat_of_is num Q.rows d0 h'.1, eps_of_is num d1 h'.2.1,
      twos_of_along num Q.k ds h'.2.2 (by simp only [List.length_cons] at hl; omega)]
  | [], _, hl => exact absurd hl (by simp only [List.length_nil]; omega)
  | [_], _, hl => exact absurd hl (by simp only [List.length_cons, List.length_nil]; omega)

/-- **AT ANY PIECE WHOSE BLOCK DECLARES K10's ROUNDS**, whatever its state. -/
theorem piece_ds {Cl' σ Cl W : Type} {C : CK} {F : Frame} (p : Piece C F σ Cl W)
    (num : Fmt.TreeSource → ℕ) (Q : Par) (h1 : Q.workField = 0) (h2 : Q.workClose = 0)
    (hr : p.b.rounds = (kind (Cl := Cl') Q).rounds) (h : Along (RoundIs num) p.b.rounds p.ds)
    (hl : p.ds.length = 2 + Q.k) : p.ds = dBat Q.rows :: dEps :: List.replicate Q.k dTwo := by
  rw [hr] at h
  exact ds_of_along num Q h1 h2 p.ds h hl

/-- **AT A DESCRIPTION**: where its data return and the three rows of pieces are the maker's, every
piece of the first row whose block declares K10's rounds, and which has as many data, has the law's
data. -/
theorem k10_data_at_desc {Cl' : Type} (Xi : Type) (Fd : FileDescription Xi) (file : String) (D : WholeD)
    (hD : Fd.data file = .ok D) (C : CK) (Y S₁ S₂ S₃ X₁ X₂ Cl W : Type)
    (T : Three C D (allOf D) Y S₁ S₂ S₃ X₁ X₂ Cl W) (b₁ : Block S₁ Cl) (l₁ : List (Block S₁ Cl))
    (b₂ : Block S₂ Cl) (l₂ : List (Block S₂ Cl)) (b₃ : Block S₃ Cl) (l₃ : List (Block S₃ Cl))
    rest₁ rest₂ rest₃ (r : Fmt.RoundView)
    (g₁ : (b₁ :: l₁).map (·.rounds) = Fd.first.blocksInOrder.map (·.rounds))
    (g₂ : (b₂ :: l₂).map (·.rounds) = Fd.shared.blocksInOrder.map (·.rounds))
    (g₃ : (b₃ :: l₃).map (·.rounds) = Fd.second.blocksInOrder.map (·.rounds))
    (hc : T.IsCut b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r) (Q : Par) (h1 : Q.workField = 0)
    (h2 : Q.workClose = 0) :
    ∀ p ∈ T.p₁ :: T.l₁, p.b.rounds = (kind (Cl := Cl') Q).rounds → p.ds.length = 2 + Q.k →
      p.ds = dBat Q.rows :: dEps :: List.replicate Q.k dTwo := fun p hp hr hl =>
  piece_ds p _ Q h1 h2 hr
    ((stretchOfData Xi Fd file D hD C Y S₁ S₂ S₃ X₁ X₂ Cl W T b₁ l₁ b₂ l₂ b₃ l₃ rest₁ rest₂ rest₃ r
      g₁ g₂ g₃ hc).1 p hp) hl

/-- **FROM THE LIFTED PIECE TO THE LAW's**: q a piece over the pair (what was handed to the chain,
the verifier's state) with the law's data and nothing put back: the piece over the bare state with
b under the words' test, q's base, data and errors, which hands the witness on, IS pieceOn b at that
extractor. (K10's law at the table's relations wants another extractor: see the head.) -/
theorem bare_is_on {P₀ Cl W : Type} {F : Frame}
    (q : Piece (ckP .two) F (P₀ × VerifiableInference.Desc.First.S) Cl W)
    (b : Block VerifiableInference.Desc.First.S Cl) (rows k : ℕ)
    (hd : q.ds = dBat rows :: dEps :: List.replicate k dTwo) (hk : q.back = []) :
    ∃ err, (⟨below b, q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) F VerifiableInference.Desc.First.S Cl W) =
      pieceOn b q.base (dBat rows) dEps dTwo k (fun _ _ w => w) err := by
  rcases q with ⟨qb, base, ds, back, ext, err⟩
  simp only at hd hk
  subst hd hk
  exact ⟨err, rfl⟩

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.bat_of_is
#print axioms VerifiableInference.Desc.First.Close.eps_of_is
#print axioms VerifiableInference.Desc.First.Close.two_of_is
#print axioms VerifiableInference.Desc.First.Close.ds_of_along
#print axioms VerifiableInference.Desc.First.Close.piece_ds
#print axioms VerifiableInference.Desc.First.Close.k10_data_at_desc
#print axioms VerifiableInference.Desc.First.Close.bare_is_on
