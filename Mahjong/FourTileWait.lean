import Mahjong.Wait

/-!
# 4枚手牌の待ち分類

4枚手牌は、和了牌を1枚加えると「1面子1雀頭」になる最小の待ち解析単位である。
待ち分類そのものは `Mahjong.Wait` に置き、このモジュールは4枚ケースの定数と
互換名を提供する。
-/

/-- 4枚待ちに含まれる完成面子の数。 -/
abbrev fourTileMentsuCount : Nat := 1

/-- 1面子を含む通常形聴牌の手牌枚数。 -/
abbrev fourTileHandSize : Nat := standardTenpaiHandSize fourTileMentsuCount

/-- 4枚ケースで使う抽出候補名。互換性とテスト名のために残す。 -/
abbrev FourTileExtraction := WaitExtraction

/-- 4枚ケースで使う待ち分類名。互換性とテスト名のために残す。 -/
abbrev FourTileWaitKind := WaitKind

/-- 4枚ケースで使う曖昧性名。互換性とテスト名のために残す。 -/
abbrev FourTileAmbiguity := WaitAmbiguity

/-- 4枚ケースで使う還元可能性名。互換性とテスト名のために残す。 -/
abbrev FourTileReducibility := WaitReducibility

/-- 4枚ケースで使う分類ラベル名。互換性とテスト名のために残す。 -/
abbrev FourTileClassification := WaitClassification
