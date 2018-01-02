import Control.Monad (forM_)
import Data.Plur
import EasyTest
import Focusing
import Focusing.Examples

main :: IO ()
main = run suite

numTerms :: Type -> Maybe Int
numTerms f = do
  case runM (search f) of
    Left err   -> Nothing
    Right plur -> Just (count plur)

suite :: Test ()
suite = forM_ examples $ \(Example desc count formula) ->
  scope desc $ expect (numTerms formula == Just count)
