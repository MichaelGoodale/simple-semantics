from itertools import product, chain, combinations
from typing import Mapping, Optional
from dataclasses import dataclass


@dataclass
class VerbalEvent:
    agent: str
    patient: str


@dataclass
class Scenario:
    present_entities: str
    events: Mapping[str, list[VerbalEvent]]

    def get_events(self, verb_concept: str) -> list[VerbalEvent]:
        return self.events[verb_concept]


MAX_GRAMMAR_LENGTH = 7
e_types = set("jpms")
predicates = set("SH")
alphabet = set(["John", "Mary", "Phil", "Sue", "sees", "hears"])
data = [
    (
        "John sees Mary",
        Scenario("jmps", {"S": [VerbalEvent("j", "m")], "H": [VerbalEvent("p", "s")]}),
    ),
    (
        "Phil hears Sue",
        Scenario("jmps", {"S": [VerbalEvent("j", "m")], "H": [VerbalEvent("p", "s")]}),
    ),
    (
        "Phil hears Mary",
        Scenario("jmps", {"S": [VerbalEvent("j", "m")], "H": [VerbalEvent("p", "m")]}),
    ),
]


possible_nouns = product(alphabet, e_types)
possible_verbs = product(alphabet, predicates)


def is_true(datum, lexical_entries) -> Optional[bool]:
    string, scenario = datum
    first, middle, last = string.split(" ")

    firsts = []
    middles = []
    lasts = []
    for w, lamb in lexical_entries:
        if first == w and lamb in e_types and lamb in scenario.present_entities:
            firsts.append((w, lamb))
        if middle == w and lamb in predicates and lamb in scenario.events:
            middles.append((w, lamb))
        if last == w and lamb in e_types and lamb in scenario.present_entities:
            lasts.append((w, lamb))
    if len(firsts) == 0 or len(middles) == 0 or len(lasts) == 0:
        return False

    valid_meaning = False
    for _middle_word, middle_verb_concept in middles:
        for event in scenario.get_events(middle_verb_concept):
            good_first = any(first_lambda == event.agent for _, first_lambda in firsts)
            good_last = any(last_lambda == event.patient for _, last_lambda in lasts)
            valid_meaning = valid_meaning or (good_first and good_last)
    return valid_meaning


all_grammars = list(possible_nouns) + list(possible_verbs)
for r in range(MAX_GRAMMAR_LENGTH):
    for grammar in combinations(all_grammars, r=r):
        if all(is_true(d, grammar) for d in data):
            print(grammar)
