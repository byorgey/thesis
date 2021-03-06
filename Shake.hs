import           Control.Applicative        (liftA2, (<$>))
import           Control.Monad              (when)
import           Data.Char                  (isSpace)
import           Data.List                  (isPrefixOf)
import           Data.List.Split
import           Development.Shake
import           Development.Shake.FilePath

lhs2TeX  = "lhs2TeX"
pdflatex = "pdflatex"
rubber   = "rubber"
bibtex   = "bibtex"

main = shake shakeOptions $ do

    want ["thesis.pdf"]

    "*.tex" *> \output -> do
        let input = replaceExtension output "lhs"
        e <- doesFileExist input
        when e $ do
          need [input]
          cmd "lhs2TeX --poly -o" [output] [input]

    "*.pdf" *> \output -> do
        let input = replaceExtension output "tex"
        includes <- map extractArg . filter isInclude <$> readFileLines input
        need (map (<.> "tex") includes)

        pkgs <- getDirectoryFiles "" ["*.sty"]
        need pkgs

        () <- cmd [pdflatex] "--enable-write18" [input]
        () <- cmd [pdflatex] "--enable-write18" [input]
        () <- cmd [bibtex] [dropExtension input]
        () <- cmd [pdflatex] "--enable-write18" [input]
        return ()

isInclude = liftA2 (||) ("\\include" `isPrefixOf`) ("\\input" `isPrefixOf`) . dropWhile isSpace

extractArg = (!!1) . splitOneOf "{}"
