import Development.Shake
import Development.Shake.FilePath

lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
rubber   = "rubber"

main = shake shakeOptions $ do

    want ["proposal.pdf"]

    "*.tex" *> \output -> do
        let input = replaceExtension output "lhs"
        need [input]
        system' lhs2TeX $ ["-o", output] ++ [input]

    "*.pdf" *> \output -> do
        let input = replaceExtension output "tex"
        need [input, "Diagrams.hs"]
        system' pdflatex $ ["--enable-write18", input]
        system' pdflatex $ ["--enable-write18", input]
