"""Parser registry.

Add new source formats by creating a parser module and registering its class
here. The common engine in unified.parser handles ordering, confidence,
source hints, and safe fallback behavior.
"""

from .capture import CaptureParser
from .character_catcher import CharacterCatcherParser
from .generic import GenericParser
from .grab import GrabParser
from .hallow import HallowParser
from .kairo import KairoParser
from .senpai import SenpaiParser
from .smash import SmashParser
from .takers import TakersParser
from .waifux import WaifuxParser

PARSERS = (
    CaptureParser,
    HallowParser,
    WaifuxParser,
    KairoParser,
    CharacterCatcherParser,
    SenpaiParser,
    GrabParser,
    TakersParser,
    SmashParser,
    GenericParser,
)

PARSER_MAP = {parser.name: parser for parser in PARSERS}

__all__ = ["PARSERS", "PARSER_MAP"]
