# encoding: utf-8
"""Copyright (C) 2013 COLDWELL AG

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

This program is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.
"""

import random
from gevent.pool import Group
from gevent.lock import Semaphore

from . import manager, this, util
from ..cache import CachedDict
from ..api import proto

cache = CachedDict(3600)

class Query(object):
    def __init__(self, id, query):
        self.id = id
        self.query = query
        self._display = None

        self.contexts = list()

        self.lock = Semaphore()
        self._i = 0

    def next_result_ctx(self):
        try:
            ctx = self.contexts[self._i]
            self._i += 1
            return ctx
        except IndexError:
            self._i = 0
            return self.next_result_ctx()

    def remove_ctx(self, ctx):
        i = self.contexts.index(ctx)
        if i <= self._i:
            self._i -= 1
        self.contexts.remove(ctx)

    @property
    def more(self):
        if self.contexts:
            return True
        return False

    @property
    def display(self):
        if self._display is not None:
            return self._display
        weights = dict(
            list=0,
            thumbs=1)
        for ctx in self.contexts:
            if self._display is None or weights[ctx.sub['display']] < weights[self._display]:
                self._display = ctx.sub['display']
        if self._display is None:
            self._display = 'list'
        return self._display
        
        
def _add_result(self, title=None, thumb=None, duration=None, url=None, description=None, extra=None, name=None):
    from .. import core
    try:
        if url is None:
            exists = 0
        else:
            exists = core.url_exists(url) and 1 or 0
    except TypeError:
        exists = 0
        url = None
    if url and extra is not None:
        url = util.add_extra(url, extra)
    if thumb is not None:
        self.display = "thumbs"
    self.results.append([name or "http", title, thumb, duration, url, description, exists])

class Context(object):
    def __init__(self, name, tags):
        self.name = name
        self.sub = self.plugin.search
        if self.sub is None:
            raise ValueError('plugin {} has no search method'.format(name))
        self.tags = tags
        self.position = None
        self.next = 0

        self.results = list()

    def add_result(self, *args, **kwargs):
        kwargs.setdefault("name", self.name)
        _add_result(self, *args, **kwargs)

    @property
    def plugin(self):
        try:
            plugin = manager.find_by_name(self.name)
        except KeyError:
            plugin = None
        if plugin is None:
            raise ValueError('plugin {} not found'.format(self.name))
        return plugin
        
class Input(object):
    def __init__(self, name, display="list", icon=None):
        self.name = name
        self.display = display
        if hasattr(this.localctx, "hoster") and not icon:
            icon = this.localctx.hoster.name
        self.icon = icon
        self.id = random.randint(1, 100000)
        self.results = []
        self.sent = False
        
    def add_result(self, *args, **kwargs):
        assert not self.sent
        kwargs.setdefault("name", self.icon)
        _add_result(self, *args, **kwargs)

    __call__ = add_result

    def send(self):
        meta = dict(name=self.name, display=self.display, id=self.id, icon=self.icon)
        payload = dict(meta=meta, result=self.results)
        #print "sending payload", payload
        proto.send("frontend", "search.open_tab", payload=payload)
        self.sent = True
    
    close = send

    def __enter__(self):
        return self
    
    def __exit__(self, etype, evalue, etrace):
        if self.results and not etype:
            self.send()

def _run(responder, search, ctx, todo):
    plugin = ctx.plugin
    ctx.account = plugin.get_account('search', None)
    ctx.position = ctx.next
    ctx.next = None
    try:
        if (not search.query or search.query=="_EMPTY") and plugin.search.get("empty"):
            plugin.on_search_empty(ctx)
        else:
            plugin.on_search(ctx, search.query)
    finally:
        del ctx.account
        todo[ctx.name] = 1
        if responder is not None:
            progress = int((float(sum(todo.values()))/len(todo))*100)
            responder.send({'progress': progress}, 'search.progress')

def _search(responder, id, search, max_results):
    todo = dict()
    group = Group()
    for ctx in search.contexts:
        if len(ctx.results) > max_results/len(search.contexts):
            continue
        todo[ctx.name] = 0
        group.spawn(_run, responder, search, ctx, todo)
    group.join()

    for ctx in search.contexts[:]:
        if not ctx.results:
            search.remove_ctx(ctx)

    results = list()
    while search.contexts and (max_results is None or len(results) < max_results):
        ctx = search.next_result_ctx()
        if not ctx.results:
            break
        results.append(ctx.results.pop(0))

    display = search.display

    for ctx in search.contexts[:]:
        if ctx.next is None:
            search.remove_ctx(ctx)

    if search.more:
        cache[search.id] = search
    elif search.id in cache:
        del cache[search.id]

    return dict(id=id, search_id=search.id, display=display, more=search.more, results=results)

def search(responder, id, search_id, plugins, query, tags, max_results=50):
    search = Query(search_id, query)
    with search.lock:
        for plugin in plugins:
            search.contexts.append(Context(plugin, tags))
        return _search(responder, id, search, max_results)

def search_more(responder, id, search_id, max_results=50):
    if search_id not in cache:
        return dict(id=id, search_id=search_id, display=None, more=False, results=[])
    search = cache[search_id]
    with search.lock:
        return _search(responder, id, search, max_results)
