import Data.Aeson

do name <- v .: "name"
   age  <- v .: "age"
   pure (Person name age)