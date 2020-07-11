module Spice

import NetList

%default total

data ElementType : Type where
  XSPICECodeModel : ElementType
  BehaviouralSource : ElementType
  Capacitor : ElementType
  Diode : ElementType
  VCVS : ElementType
  CCCS : ElementType
  VCCS : ElementType
  CCVS : ElementType
  CurrentSource : ElementType
  JFET : ElementType
  CoupledInductors : ElementType
  Inductor : ElementType
  MOSFET : ElementType
  NumericalForGSS : ElementType
  LossyTransmissionLine : ElementType
  CPL : ElementType
  BJT : ElementType
  Resistor : ElementType
  VoltageControlledSwitch : ElementType
  LosslessTransmissionLine : ElementType
  UniformlyDistributedRCLine : ElementType
  VoltageSource : ElementType
  CurrentControlledSwitch : ElementType
  Subcircuit : ElementType
  TXL : ElementType
  MESFET : ElementType

elementTypeNameLetter : ElementType -> Char
elementTypeNameLetter XSPICECodeModel            = 'A'
elementTypeNameLetter BehaviouralSource          = 'B'
elementTypeNameLetter Capacitor                  = 'C'
elementTypeNameLetter Diode                      = 'D'
elementTypeNameLetter VCVS                       = 'E'
elementTypeNameLetter CCCS                       = 'F'
elementTypeNameLetter VCCS                       = 'G'
elementTypeNameLetter CCVS                       = 'H'
elementTypeNameLetter CurrentSource              = 'I'
elementTypeNameLetter JFET                       = 'J'
elementTypeNameLetter CoupledInductors           = 'K'
elementTypeNameLetter Inductor                   = 'L'
elementTypeNameLetter MOSFET                     = 'M'
elementTypeNameLetter NumericalForGSS            = 'N'
elementTypeNameLetter LossyTransmissionLine      = 'O'
elementTypeNameLetter CPL                        = 'P'
elementTypeNameLetter BJT                        = 'Q'
elementTypeNameLetter Resistor                   = 'R'
elementTypeNameLetter VoltageControlledSwitch    = 'S'
elementTypeNameLetter LosslessTransmissionLine   = 'T'
elementTypeNameLetter UniformlyDistributedRCLine = 'U'
elementTypeNameLetter VoltageSource              = 'V'
elementTypeNameLetter CurrentControlledSwitch    = 'W'
elementTypeNameLetter Subcircuit                 = 'X'
elementTypeNameLetter TXL                        = 'Y'
elementTypeNameLetter MESFET                     = 'Z'

data Node : Type where
  Ground : Node
  MkNode : Bits64 -> Node

data Parameter : Type

data Line : Type where
  Instance : ElementType -> String -> List Node -> List Parameter -> Line

