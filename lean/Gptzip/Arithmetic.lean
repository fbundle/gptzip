import Std

namespace Gptzip

/-- Integer bounds for a finite vocabulary, with a positive mass for each token. -/
structure CDF where
  size : Nat
  total : Nat
  bound : Nat → Nat
  positive : 0 < total
  first : bound 0 = 0
  last : bound size = total
  increasing : ∀ i j, i < j → j ≤ size → bound i < bound j

abbrev Model := List Nat → CDF

/-- The half-open rational interval `[lo / scale, hi / scale)`. -/
structure Interval where
  lo : Nat
  hi : Nat
  scale : Nat
  ordered : lo < hi
  bounded : hi ≤ scale

def initial : Interval := ⟨0, 1, 1, by decide, by decide⟩

theorem CDF.bound_le (cdf : CDF) {i : Nat} (h : i ≤ cdf.size) :
    cdf.bound i ≤ cdf.total := by
  rcases Nat.lt_or_eq_of_le h with lt | rfl
  · rw [← cdf.last]
    exact Nat.le_of_lt (cdf.increasing i cdf.size lt (Nat.le_refl _))
  · exact Nat.le_of_eq cdf.last

private theorem increasing_of_adjacent {bound : Nat → Nat} {size : Nat}
    (adjacent : ∀ i, i < size → bound i < bound (i + 1)) :
    ∀ i j, i < j → j ≤ size → bound i < bound j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
    intro ij js
    have last := adjacent j js
    by_cases eq : i = j
    · simpa [eq] using last
    · exact Nat.lt_trans (ih (by omega) (by omega)) last

/-- Validate a table of cumulative bounds, including both endpoints. -/
def CDF.ofArray (bounds : Array Nat) : Option CDF :=
  let size := bounds.size - 1
  let bound := fun i => bounds[i]?.getD 0
  let total := bound size
  if first : bound 0 = 0 then
    if positive : 0 < total then
      if adjacent : (List.range size).all (fun i => decide (bound i < bound (i + 1))) then
        some ⟨size, total, bound, positive, first, rfl,
          increasing_of_adjacent fun i hi =>
            of_decide_eq_true (List.all_eq_true.mp adjacent i (List.mem_range.mpr hi))⟩
      else none
    else none
  else none

def narrow (r : Interval) (cdf : CDF) (token : Nat) (valid : token < cdf.size) :
    Interval where
  lo := r.lo * cdf.total + (r.hi - r.lo) * cdf.bound token
  hi := r.lo * cdf.total + (r.hi - r.lo) * cdf.bound (token + 1)
  scale := r.scale * cdf.total
  ordered := by
    have strict := cdf.increasing token (token + 1) (by omega) valid
    have width : 0 < r.hi - r.lo := by have := r.ordered; omega
    exact Nat.add_lt_add_left (Nat.mul_lt_mul_of_pos_left strict width) _
  bounded := by
    calc
      _ ≤ r.lo * cdf.total + (r.hi - r.lo) * cdf.total :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ (cdf.bound_le valid)) _
      _ = r.hi * cdf.total := by rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt r.ordered)]
      _ ≤ _ := Nat.mul_le_mul_right _ r.bounded

/-- The finite binary fraction represented by a payload. -/
structure Point where
  numerator : Nat
  denominator : Nat
  positive : 0 < denominator

def Contains (r : Interval) (p : Point) : Prop :=
  r.lo * p.denominator ≤ p.numerator * r.scale ∧
    p.numerator * r.scale < r.hi * p.denominator

instance (r : Interval) (p : Point) : Decidable (Contains r p) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem narrow_contains {r : Interval} {cdf : CDF} {token : Nat}
    {valid : token < cdf.size} {p : Point}
    (h : Contains (narrow r cdf token valid) p) : Contains r p := by
  unfold Contains at *
  change (r.lo * cdf.total + _) * p.denominator ≤
      p.numerator * (r.scale * cdf.total) ∧
      p.numerator * (r.scale * cdf.total) < (r.lo * cdf.total + _) * p.denominator at h
  have lower : r.lo * cdf.total * p.denominator ≤ p.numerator * (r.scale * cdf.total) :=
    Nat.le_trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)) h.1
  have upperBound :
      r.lo * cdf.total + (r.hi - r.lo) * cdf.bound (token + 1) ≤ r.hi * cdf.total := by
    calc
      _ ≤ r.lo * cdf.total + (r.hi - r.lo) * cdf.total :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ (cdf.bound_le valid)) _
      _ = _ := by rw [← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt r.ordered)]
  have upper := Nat.lt_of_lt_of_le h.2 (Nat.mul_le_mul_right p.denominator upperBound)
  rw [Nat.mul_assoc, Nat.mul_comm cdf.total p.denominator, ← Nat.mul_assoc,
    ← Nat.mul_assoc] at lower upper
  exact ⟨(Nat.le_of_mul_le_mul_right lower cdf.positive),
    (Nat.lt_of_mul_lt_mul_right upper)⟩

/-- Find the greatest boundary at or below the point. The right endpoint is exclusive. -/
private def search (atOrBelow : Nat → Bool) (lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := lo + (hi - lo) / 2
    if atOrBelow mid then search atOrBelow mid hi else search atOrBelow lo mid
  else lo
termination_by hi - lo
decreasing_by all_goals omega

private theorem search_correct (atOrBelow : Nat → Bool) (lo hi target : Nat)
    (inRange : lo ≤ target ∧ target < hi)
    (threshold : ∀ i, lo ≤ i → i < hi → atOrBelow i = decide (i ≤ target)) :
    search atOrBelow lo hi = target := by
  rw [search.eq_def]
  split
  next wide =>
    let mid := lo + (hi - lo) / 2
    have midLo : lo < mid := by dsimp [mid]; omega
    have midHi : mid < hi := by dsimp [mid]; omega
    change (if atOrBelow mid then search atOrBelow mid hi else search atOrBelow lo mid) = target
    rw [threshold mid (Nat.le_of_lt midLo) midHi]
    by_cases h : mid ≤ target
    · simp only [h, decide_true, if_true]
      exact search_correct atOrBelow mid hi target ⟨h, inRange.2⟩
        (fun i ilo ihi => threshold i (by omega) ihi)
    · simp only [h, decide_false]
      exact search_correct atOrBelow lo mid target ⟨inRange.1, by omega⟩
        (fun i ilo ihi => threshold i ilo (by omega))
  next => omega
termination_by hi - lo
decreasing_by all_goals omega

private def boundary (r : Interval) (cdf : CDF) (i : Nat) : Nat :=
  r.lo * cdf.total + (r.hi - r.lo) * cdf.bound i

private theorem boundary_mono (r : Interval) (cdf : CDF) {i j : Nat}
    (ij : i ≤ j) (valid : j ≤ cdf.size) : boundary r cdf i ≤ boundary r cdf j := by
  rcases Nat.lt_or_eq_of_le ij with lt | rfl
  · exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_of_lt (cdf.increasing i j lt valid))) _
  · exact Nat.le_refl _

def select (r : Interval) (cdf : CDF) (p : Point) : Option (Fin cdf.size) :=
  let index := search (fun i => decide (boundary r cdf i * p.denominator ≤
    p.numerator * (r.scale * cdf.total))) 0 cdf.size
  if valid : index < cdf.size then
    if Contains (narrow r cdf index valid) p then some ⟨index, valid⟩ else none
  else none

theorem select_correct {r : Interval} {cdf : CDF} {p : Point} (t : Fin cdf.size)
    (h : Contains (narrow r cdf t.val t.isLt) p) : select r cdf p = some t := by
  have lo : boundary r cdf t.val * p.denominator ≤ p.numerator * (r.scale * cdf.total) := h.1
  have hi : p.numerator * (r.scale * cdf.total) < boundary r cdf (t.val + 1) * p.denominator := h.2
  have found := search_correct
    (fun i => decide (boundary r cdf i * p.denominator ≤ p.numerator * (r.scale * cdf.total)))
    0 cdf.size t.val ⟨Nat.zero_le _, t.isLt⟩ (by
      intro i _ valid
      by_cases before : i ≤ t.val
      · have lower := Nat.le_trans (Nat.mul_le_mul_right p.denominator
          (boundary_mono r cdf before (Nat.le_of_lt t.isLt))) lo
        simp [before, lower]
      · have upper := Nat.lt_of_lt_of_le hi (Nat.mul_le_mul_right p.denominator
          (boundary_mono r cdf (Nat.succ_le_of_lt (Nat.lt_of_not_ge before)) (Nat.le_of_lt valid)))
        simp [before, Nat.not_le_of_lt upper])
  simp [select, found, t.isLt, h]

/-- The context is stored in reverse order so extending a context takes constant time. -/
def encodeFrom (model : Model) (context : List Nat) (r : Interval) :
    List Nat → Option Interval
  | [] => some r
  | t :: ts =>
    let cdf := model context
    if valid : t < cdf.size then
      encodeFrom model (t :: context) (narrow r cdf t valid) ts
    else none

def decodeFrom (model : Model) (context : List Nat) (r : Interval) (p : Point) :
    Nat → Option (List Nat)
  | 0 => some []
  | n + 1 => do
    let cdf := model context
    let t ← select r cdf p
    let ts ← decodeFrom model (t.val :: context) (narrow r cdf t.val t.isLt) p n
    pure (t.val :: ts)

theorem encodeFrom_contains {model : Model} {context : List Nat} {r final : Interval}
    {tokens : List Nat} {p : Point}
    (encoded : encodeFrom model context r tokens = some final)
    (inside : Contains final p) : Contains r p := by
  induction tokens generalizing context r with
  | nil =>
    simp [encodeFrom] at encoded
    exact encoded ▸ inside
  | cons t ts ih =>
    simp only [encodeFrom] at encoded
    split at encoded
    · exact narrow_contains (ih encoded)
    · contradiction

theorem decodeFrom_encodeFrom {model : Model} {context : List Nat} {r final : Interval}
    {tokens : List Nat} {p : Point}
    (encoded : encodeFrom model context r tokens = some final)
    (inside : Contains final p) :
    decodeFrom model context r p tokens.length = some tokens := by
  induction tokens generalizing context r with
  | nil => rfl
  | cons t ts ih =>
    simp only [encodeFrom] at encoded
    split at encoded
    next valid =>
      have selected :=
        select_correct ⟨t, valid⟩ (encodeFrom_contains encoded inside)
      simp [decodeFrom, selected, ih encoded]
    next => contradiction


/-- A binary word of exactly `width` bits, with leading zeros retained by the width. -/
structure Word where
  width : Nat
  value : Nat
  fits : value < 2 ^ width

def Word.point (word : Word) : Point :=
  ⟨word.value, 2 ^ word.width, Nat.pow_pos (by decide)⟩

/-- Enough bits to make the dyadic grid finer than the interval's width. -/
def Interval.precision (r : Interval) : Nat :=
  (r.scale / (r.hi - r.lo)).log2 + 1

private theorem chooseWord_bounds (r : Interval) :
    let d := 2 ^ r.precision
    let v := r.lo * d / r.scale + 1
    r.lo * d ≤ v * r.scale ∧ v * r.scale < r.hi * d := by
  dsimp
  let d := 2 ^ r.precision
  change r.lo * d ≤ (r.lo * d / r.scale + 1) * r.scale ∧
    (r.lo * d / r.scale + 1) * r.scale < r.hi * d
  have scalePos : 0 < r.scale := Nat.lt_of_lt_of_le (Nat.zero_lt_of_lt r.ordered) r.bounded
  have widthPos : 0 < r.hi - r.lo := Nat.sub_pos_of_lt r.ordered
  have quotientPos : 0 < r.scale / (r.hi - r.lo) :=
    Nat.div_pos (Nat.le_trans (Nat.sub_le _ _) r.bounded) widthPos
  have grid : r.scale / (r.hi - r.lo) < d :=
    (Nat.log2_lt (Nat.ne_of_gt quotientPos)).mp (Nat.lt_succ_self _)
  have roomy : r.scale < d * (r.hi - r.lo) := (Nat.div_lt_iff_lt_mul widthPos).mp grid
  constructor
  · have strict := Nat.lt_mul_div_succ (r.lo * d) scalePos
    rw [Nat.mul_comm r.scale] at strict
    exact Nat.le_of_lt strict
  · rw [Nat.add_mul, Nat.one_mul]
    calc
      _ ≤ r.lo * d + r.scale := Nat.add_le_add_right (Nat.div_mul_le_self _ _) _
      _ < r.lo * d + d * (r.hi - r.lo) := Nat.add_lt_add_left roomy _
      _ = r.hi * d := by
        rw [Nat.mul_comm d, ← Nat.add_mul, Nat.add_sub_of_le (Nat.le_of_lt r.ordered)]

/-- Pick a dyadic point strictly below the upper bound of the final interval. -/
def chooseWord (r : Interval) : Word where
  width := r.precision
  value := r.lo * 2 ^ r.precision / r.scale + 1
  fits := by
    have upper := (chooseWord_bounds r).2
    apply Nat.lt_of_mul_lt_mul_right (a := r.scale)
    apply Nat.lt_of_lt_of_le upper
    rw [Nat.mul_comm (2 ^ r.precision)]
    exact Nat.mul_le_mul_right _ r.bounded

theorem chooseWord_contains (r : Interval) : Contains r (chooseWord r).point :=
  chooseWord_bounds r

/-- A counted frame in the exact arithmetic format. -/
structure Frame where
  tokenCount : Nat
  payload : Word

def encode (model : Model) (tokens : List Nat) : Option Frame := do
  let final ← encodeFrom model [] initial tokens
  pure ⟨tokens.length, chooseWord final⟩

def decode (model : Model) (frame : Frame) : Option (List Nat) :=
  decodeFrom model [] initial frame.payload.point frame.tokenCount

/-- Any successfully encoded sequence, including the empty sequence, decodes exactly. -/
theorem decode_encode {model : Model} {tokens : List Nat} {frame : Frame}
    (encoded : encode model tokens = some frame) :
    decode model frame = some tokens := by
  unfold encode at encoded
  cases result : encodeFrom model [] initial tokens with
  | none => simp [result] at encoded
  | some final =>
    simp [result] at encoded
    subst frame
    exact decodeFrom_encodeFrom result (chooseWord_contains final)


/-- Each token must be in the vocabulary for the context where it is coded. -/
def Valid (model : Model) (context : List Nat) : List Nat → Prop
  | [] => True
  | token :: rest => token < (model context).size ∧ Valid model (token :: context) rest

theorem encodeFrom_succeeds (model : Model) (context : List Nat) (r : Interval)
    (tokens : List Nat) (valid : Valid model context tokens) :
    ∃ final, encodeFrom model context r tokens = some final := by
  induction tokens generalizing context r with
  | nil => exact ⟨r, rfl⟩
  | cons token rest ih =>
    have ht := valid.1
    obtain ⟨final, encoded⟩ :=
      ih (token :: context) (narrow r (model context) token ht) valid.2
    exact ⟨final, by simpa [encodeFrom, ht] using encoded⟩

private def emitBits : Nat → Nat → List Bool
  | 0, _ => []
  | width + 1, value => (value % 2 == 1) :: emitBits width (value / 2)

private def readBits : List Bool → Nat
  | [] => 0
  | bit :: rest => bit.toNat + 2 * readBits rest

private theorem emitBits_length (width value : Nat) :
    (emitBits width value).length = width := by
  induction width generalizing value with
  | zero => rfl
  | succ width ih => simp [emitBits, ih]

private theorem readBits_fits (bits : List Bool) : readBits bits < 2 ^ bits.length := by
  induction bits with
  | nil => decide
  | cons bit rest ih =>
    simp only [readBits, List.length_cons, Nat.pow_succ]
    cases bit <;> simp only [Bool.toNat] <;> change _ < _ <;> simp <;> omega

private theorem readBits_emitBits (width value : Nat) (fits : value < 2 ^ width) :
    readBits (emitBits width value) = value := by
  induction width generalizing value with
  | zero =>
    simp only [Nat.pow_zero] at fits
    change 0 = value
    omega
  | succ width ih =>
    have halfFits : value / 2 < 2 ^ width :=
      (Nat.div_lt_iff_lt_mul (by decide)).mpr (by simpa only [Nat.pow_succ] using fits)
    have lowBit : (value % 2 == 1).toNat = value % 2 := by
      by_cases h : value % 2 = 1
      · simp [h]
      · have zero : value % 2 = 0 := by omega
        simp [zero]
    simp only [emitBits, readBits, lowBit, ih _ halfFits]
    omega

/-- Emit the least significant bit first, including all leading zeros of the word. -/
def Word.toBits (word : Word) : List Bool :=
  emitBits word.width word.value

def Word.ofBits (bits : List Bool) : Word :=
  ⟨bits.length, readBits bits, readBits_fits bits⟩

theorem Word.ofBits_toBits (word : Word) : ofBits word.toBits = word := by
  cases word with
  | mk width value fits =>
    simp only [ofBits, toBits, emitBits_length, readBits_emitBits _ _ fits]

/-- The v1 bit-level frame carries a token count and its finite binary payload. -/
structure BitFrame where
  tokenCount : Nat
  payload : List Bool
  deriving Repr

def Frame.toBits (frame : Frame) : BitFrame :=
  ⟨frame.tokenCount, frame.payload.toBits⟩

def encodeBits (model : Model) (tokens : List Nat) : Option BitFrame :=
  (encode model tokens).map Frame.toBits

def decodeBits (model : Model) (frame : BitFrame) : Option (List Nat) :=
  decode model ⟨frame.tokenCount, Word.ofBits frame.payload⟩

theorem decodeBits_encodeBits (model : Model) (tokens : List Nat)
    (valid : Valid model [] tokens) :
    ∃ frame, encodeBits model tokens = some frame ∧ decodeBits model frame = some tokens := by
  obtain ⟨final, narrowed⟩ := encodeFrom_succeeds model [] initial tokens valid
  let frame : Frame := ⟨tokens.length, chooseWord final⟩
  have encoded : encode model tokens = some frame := by simp [encode, narrowed, frame]
  refine ⟨frame.toBits, by simp [encodeBits, encoded], ?_⟩
  simpa [decodeBits, Frame.toBits, Word.ofBits_toBits] using decode_encode encoded


/-- Pack each consecutive group of eight bits into a byte, low bit first. -/
def packBits (bits : List Bool) : List UInt8 :=
  match bits with
  | [] => []
  | bit :: rest =>
    UInt8.ofNat (readBits ((bit :: rest).take 8)) :: packBits ((bit :: rest).drop 8)
termination_by bits.length
decreasing_by simp [List.length_drop]; omega

/-- Read exactly the declared number of bits, rejecting missing bytes and nonzero padding. -/
def unpackBits (bitCount : Nat) : List UInt8 → Option (List Bool)
  | [] => if bitCount = 0 then some [] else none
  | byte :: bytes => do
    let width := min 8 bitCount
    if width = 0 ∨ 2 ^ width ≤ byte.toNat then
      none
    else
      let rest ← unpackBits (bitCount - 8) bytes
      pure (emitBits width byte.toNat ++ rest)

theorem unpackBits_byteCount {bitCount : Nat} {bytes : List UInt8} {bits : List Bool}
    (decoded : unpackBits bitCount bytes = some bits) :
    bytes.length = (bitCount + 7) / 8 := by
  induction bytes generalizing bitCount bits with
  | nil =>
    simp only [unpackBits] at decoded
    split at decoded
    · simp_all
    · contradiction
  | cons byte bytes ih =>
    simp only [unpackBits] at decoded
    split at decoded
    · contradiction
    next valid =>
      have positive : 0 < bitCount := by
        cases bitCount with
        | zero => simp at valid
        | succ n => exact Nat.succ_pos n
      cases result : unpackBits (bitCount - 8) bytes with
      | none => simp [result] at decoded
      | some rest =>
        have count := ih result
        simp only [List.length_cons]
        omega

private theorem emitBits_readBits (bits : List Bool) :
    emitBits bits.length (readBits bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    have small : bit.toNat < 2 := by cases bit <;> decide
    have parity : (readBits (bit :: rest) % 2 == 1) = bit := by
      have rem : readBits (bit :: rest) % 2 = bit.toNat := by
        simp only [readBits]
        omega
      rw [rem]
      cases bit <;> decide
    have half : readBits (bit :: rest) / 2 = readBits rest := by
      simp only [readBits]
      omega
    simp only [List.length_cons, emitBits, parity, half, ih]

theorem unpackBits_packBits (bits : List Bool) :
    unpackBits bits.length (packBits bits) = some bits := by
  cases bits with
  | nil => simp [packBits, unpackBits]
  | cons bit rest =>
    let bits := bit :: rest
    let chunk := bits.take 8
    let tail := bits.drop 8
    have chunkWidth : chunk.length = min 8 bits.length := List.length_take
    have tailWidth : tail.length = bits.length - 8 := List.length_drop
    have chunkPos : 0 < chunk.length := by simp [chunkWidth, bits]; omega
    have chunkByte : readBits chunk < 2 ^ 8 :=
      Nat.lt_of_lt_of_le (readBits_fits chunk)
        (Nat.pow_le_pow_right (by decide) (by rw [chunkWidth]; exact Nat.min_le_left ..))
    have byteValue : (UInt8.ofNat (readBits chunk)).toNat = readBits chunk := by
      exact Nat.mod_eq_of_lt chunkByte
    have fits : ¬ 2 ^ chunk.length ≤ readBits chunk := Nat.not_le_of_lt (readBits_fits chunk)
    have tailRoundTrip := unpackBits_packBits tail
    rw [packBits.eq_def]
    change unpackBits bits.length (UInt8.ofNat (readBits chunk) :: packBits tail) = some bits
    simp only [unpackBits, ← chunkWidth, ← tailWidth, byteValue,
      Nat.ne_of_gt chunkPos, fits, or_self, if_false, tailRoundTrip, emitBits_readBits]
    exact congrArg some (List.take_append_drop 8 bits)
termination_by bits.length
decreasing_by simp [List.length_drop]; omega

/-- Exact arithmetic v1 frame with byte-packed payload and an explicit bit count. -/
structure PackedFrame where
  tokenCount : Nat
  bitCount : Nat
  payload : List UInt8
  deriving Repr

def BitFrame.pack (frame : BitFrame) : PackedFrame :=
  ⟨frame.tokenCount, frame.payload.length, packBits frame.payload⟩

def PackedFrame.unpack (frame : PackedFrame) : Option BitFrame :=
  (unpackBits frame.bitCount frame.payload).map (fun bits => ⟨frame.tokenCount, bits⟩)

theorem BitFrame.unpack_pack (frame : BitFrame) : frame.pack.unpack = some frame := by
  cases frame
  simp [BitFrame.pack, PackedFrame.unpack, unpackBits_packBits]

def encodePacked (model : Model) (tokens : List Nat) : Option PackedFrame :=
  (encodeBits model tokens).map BitFrame.pack

def decodePacked (model : Model) (frame : PackedFrame) : Option (List Nat) :=
  frame.unpack >>= decodeBits model

/-- A shorter byte payload is rejected when the declared bit count is retained. -/
theorem decodePacked_rejects_short_payload (model : Model) (frame : BitFrame)
    (bytes : List UInt8) (short : bytes.length < frame.pack.payload.length) :
    decodePacked model { frame.pack with payload := bytes } = none := by
  have expected := unpackBits_byteCount (unpackBits_packBits frame.payload)
  cases result : unpackBits frame.payload.length bytes with
  | none => simp [decodePacked, PackedFrame.unpack, BitFrame.pack, result]
  | some bits =>
    have actual := unpackBits_byteCount result
    change bytes.length < (packBits frame.payload).length at short
    omega

/-- Every valid token sequence encodes and round-trips through the packed frame. -/
theorem decodePacked_encodePacked (model : Model) (tokens : List Nat)
    (valid : Valid model [] tokens) :
    ∃ frame, encodePacked model tokens = some frame ∧ decodePacked model frame = some tokens := by
  obtain ⟨bits, encoded, decoded⟩ := decodeBits_encodeBits model tokens valid
  exact ⟨bits.pack, by simp [encodePacked, encoded],
    by simpa [decodePacked, BitFrame.unpack_pack] using decoded⟩

end Gptzip
