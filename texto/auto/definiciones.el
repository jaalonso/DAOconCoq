(TeX-add-style-hook
 "definiciones"
 (lambda ()
   (TeX-add-symbols
    '("teoria" 1)
    '("practica" 1)
    '("note" 1)
    '("entrada" 1)
    '("alert" 1)
    "liff"
    "lif"
    "valor")
   (LaTeX-add-environments
    "ejercicio"
    "solucion"))
 :latex)

