theory Stream
  imports Main
begin
codatatype (sset: 'a) Stream =
  SCons (shd: 'a) (stl: "'a Stream")
end