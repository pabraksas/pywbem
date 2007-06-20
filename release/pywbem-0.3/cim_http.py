#! /usr/bin/python
#
# (C) Copyright 2003, 2004 Hewlett-Packard Development Company, L.P.
#
# This program is free software; you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation; either version 2 of the License, or
# (at your option) any later version.
#   
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#   
# You should have received a copy of the GNU General Public License
# along with this program; if not, write to the Free Software
# Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.
#

# Author: Tim Potter <tpot@hp.com>
# Author: Martin Pool <mbp@hp.com>

'''
This module implements CIM operations over HTTP.

This module should not know anything about the fact that the data
being transferred is XML.  It is up to the caller to format the input
data and interpret the result.
'''

import sys, string, re, os, socket
import cim_obj

class Error(Exception):
    """This exception is raised when a transport error occurs."""
    pass

def parse_url(url):
    """Return a tuple of (host, port, ssl) from the URL parameter.
    The returned port defaults to 5988 if not specified.  SSL supports
    defaults to False if not specified."""

    host = url                          # Defaults
    port = 5988
    ssl = False

    if re.match("https", url):          # Set SSL if specified
        ssl = True
        port = 5989

    m = re.search("^https?://", url)    # Eat protocol name
    if m:
        host = url[len(m.group(0)):]

    s = string.split(host, ":")         # Set port number
    if len(s) != 1:
        host = s[0]
        port = int(s[1])

    return host, port, ssl

def wbem_request(url, data, creds, headers = [], debug = 0):
    """Send XML data over HTTP to the specified url. Return the
    response in XML.  Uses Python's build-in httplib."""

    import httplib, base64, urllib

    host, port, ssl = parse_url(url)

    if ssl:
        h = httplib.HTTPSConnection(host, port = port)
    else:
        h = httplib.HTTPConnection(host, port = port)

    h.putrequest('POST', '/cimom')

    h.putheader('Content-type', 'application/xml')
    h.putheader('Content-length', len(data))
    h.putheader('Authorization', 'Basic %s' %
                base64.encodestring('%s:%s' % (creds[0], creds[1]))[:-1])

    for hdr in headers:
        s = map(lambda x: string.strip(x), string.split(hdr, ":", 1))
        h.putheader(urllib.quote(s[0]), urllib.quote(s[1]))

    try:
        h.endheaders()
        h.send('<?xml version="1.0" encoding="utf-8" ?>\n')
        h.send(data)

        response = h.getresponse()

        if response.status != 200:
            if response.getheader('CIMError', None) is not None and \
               response.getheader('PGErrorDetail', None) is not None:
                import urllib
                raise Error(
                    'CIMError: %s: %s' %
                    (response.getheader('CIMError'),
                     urllib.unquote(response.getheader('PGErrorDetail'))))
            raise Error('HTTP error: %s' % response.reason)

    except httplib.BadStatusLine, arg:
        raise Error("The web server returned a bad status line: '%s'" % arg)
    except socket.error, arg:
        raise Error("Socket error: %s" % arg[1])
    except socket.sslerror, arg:
        raise Error("SSL error: %s" % arg[1])

    return response.read()


def get_object_header(obj):
    """Return the HTTP header required to make a CIM operation request
    using the given object.  Return None if the object does not need
    to have a header."""

    # CIMLocalNamespacePath

    if isinstance(obj, cim_obj.CIMLocalNamespacePath):
        return 'CIMObject: %s' % obj.localnamespacepath

    # CIMLocalClassPath

    if isinstance(obj, cim_obj.CIMLocalClassPath):
        return 'CIMObject: %s:%s' % (obj.localnamespacepath, obj.classname)

    # CIMInstanceName

    if isinstance(obj, cim_obj.CIMLocalInstancePath):
        hdr = 'CIMObject: %s:%s' % (obj.localnamespacepath, obj.instancename)
        return hdr

    raise TypeError('Don\'t know how to generate HTTP headers for %s' % obj)
