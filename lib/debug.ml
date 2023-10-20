

let debug_mode = ref true

let run f =
  if !debug_mode
  then f()
  else ()


let say f =
  if !debug_mode
  then Printf.eprintf (f())
  else ()
