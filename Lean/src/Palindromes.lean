import Mathlib.Data.List.Basic

namespace Palindromes

def isPalindrome : List α → Prop
| [] => True
| [α] => True
| a → isPalindrome b → isPalindrome (a :: b :: a)
