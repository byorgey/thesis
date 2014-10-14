module Proposal where

import           Diagrams.Prelude

timeline w = hcat [ vrule 1, hrule w, vrule 1 ]

totalTime = 30
thisWork = 8

if' True t = t
if' False _ = mempty

proposalDia n
  = vcat' (with & sep .~ 0.5)
    [ vcat' (with & sep .~ 0.5)
      [ text "proposal"
      , timeline totalTime # centerXY
      ]
      # alignL
    , if' (n > 1) $
      hcat
      [ vcat' (with & sep .~ 0.5)
        [ timeline thisWork # centerXY
        , text "this work"
        ]
      , if' (n > 2) $
        vcat' (with & sep .~ 0.5)
        [ timeline (30 - thisWork) # centerXY
        , text "next 5-10 years?"
        ]
      ]
      # alignL
    ]
