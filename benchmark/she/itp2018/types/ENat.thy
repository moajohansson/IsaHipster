theory ENat
  imports Main
begin
  codatatype ENat = is_zero: EZ | ESuc (epred: ENat)
end